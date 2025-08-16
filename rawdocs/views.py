import os
import json
import requests
from datetime import datetime
from PyPDF2 import PdfReader

from django.shortcuts import render, redirect, get_object_or_404
from django.core.files.base import ContentFile
from django.http import JsonResponse
from django.contrib import messages
from django.contrib.auth import authenticate, login
from django.contrib.auth.decorators import login_required, user_passes_test
from django.contrib.auth.forms import UserCreationForm
from django.contrib.auth.models import User, Group
from django.core.paginator import Paginator
from django.db import transaction, models
from django import forms
from django.views.decorators.csrf import csrf_exempt
from django.contrib.auth import views as auth_views
from django.http import HttpResponse


from .models import (
    RawDocument, MetadataLog,
    DocumentPage, AnnotationType,
    Annotation, AnnotationSession,
    AILearningMetrics, AnnotationFeedback
)
from .utils import extract_metadonnees, extract_full_text
from .annotation_utils import extract_pages_from_pdf
from .rlhf_learning import RLHFGroqAnnotator


# ——— Forms ——————————————————————————————————————————

class UploadForm(forms.Form):
    pdf_url = forms.URLField(
        required=False,
        widget=forms.URLInput(attrs={
            'placeholder': 'https://…',
            'class': 'upload-cell__input'
        })
    )
    pdf_file = forms.FileField(required=False)


class RegisterForm(UserCreationForm):
    email = forms.EmailField(required=True)
    role = forms.ChoiceField(choices=[
        ("Metadonneur", "Métadonneur"),
        ("Annotateur", "Annotateur"),
        ("Expert", "Expert"),
        ("Client", "Client"),  # ADD THIS LINE
    ], label="Profil")

    class Meta:
        model = User
        fields = ("username", "email", "role", "password1", "password2")

    def save(self, commit=True):
        user = super().save(commit)
        user.email = self.cleaned_data["email"]
        group = Group.objects.get_or_create(name=self.cleaned_data["role"])[0]  # CHANGE THIS LINE
        user.groups.add(group)
        if commit:
            user.save()
        return user


class MetadataEditForm(forms.Form):
    title = forms.CharField(required=False)
    type = forms.CharField(required=False)
    publication_date = forms.DateField(
        required=False,
        widget=forms.DateInput(attrs={'type': 'date'})
    )
    version = forms.CharField(required=False)
    source = forms.CharField(required=False)
    context = forms.CharField(required=False)
    country = forms.CharField(required=False)
    language = forms.CharField(required=False)
    url_source = forms.URLField(required=False)


# ——— Permissions ——————————————————————————————————————

def is_metadonneur(user):
    return user.groups.filter(name="Metadonneur").exists()


def is_annotateur(user):
    return user.groups.filter(name="Annotateur").exists()


def is_expert(user):
    return user.groups.filter(name="Expert").exists()


# ——— Authentication ————————————————————————————————————

from django.urls import reverse
from django.conf import settings


class CustomLoginView(auth_views.LoginView):
    template_name = 'registration/login.html'

    def get_success_url(self):
        user = self.request.user
        if user.groups.filter(name='Client').exists():
            return '/client/'  # We'll create this
        if user.groups.filter(name='Expert').exists():
            return reverse('expert:dashboard')
        if user.groups.filter(name='Annotateur').exists():
            return reverse('rawdocs:annotation_dashboard')
        if user.groups.filter(name='Metadonneur').exists():
            return reverse('rawdocs:dashboard')
        return '/'


def register(request):
    if request.method == 'POST':
        form = RegisterForm(request.POST)
        if form.is_valid():
            user = form.save()
            uname = form.cleaned_data['username']
            pwd = form.cleaned_data['password1']
            user = authenticate(username=uname, password=pwd)
            login(request, user)

            # Redirect to proper dashboard based on role
            grp = form.cleaned_data['role']
            if grp == "Metadonneur":
                return redirect('rawdocs:dashboard')  # Metadonneur dashboard
            elif grp == "Annotateur":
                return redirect('rawdocs:annotation_dashboard')  # Annotateur dashboard
            elif grp == "Expert":
                return redirect('expert:dashboard')  # Expert dashboard
            elif grp == "Client":
                return redirect('/client/')  # Client dashboard
            else:
                return redirect('rawdocs:dashboard')  # Fallback
    else:
        form = RegisterForm()
    return render(request, 'registration/register.html', {'form': form})


# ——— Métadonneur Views ——————————————————————————————

@login_required(login_url='rawdocs:login')
@user_passes_test(is_metadonneur)
def dashboard_view(request):
    docs = RawDocument.objects.filter(owner=request.user).order_by('-created_at')
    context = {
        'documents': docs,
        'total_scrapped': docs.count(),
        'total_planned': 150,
        'total_completed': 0,
        'in_progress': 12,
        'pie_data': json.dumps([15, 8, 12, 5, 3]),
        'bar_data': json.dumps([150, docs.count(), 0, 12]),
    }
    return render(request, 'rawdocs/dashboard.html', context)


@login_required(login_url='rawdocs:login')
@user_passes_test(is_metadonneur)
def upload_pdf(request):
    form = UploadForm(request.POST or None, request.FILES or None)
    context = {'form': form}

    if request.method == 'POST' and form.is_valid():
        try:
            # Priorité au fichier local
            if form.cleaned_data.get('pdf_file'):
                f = form.cleaned_data['pdf_file']
                rd = RawDocument(owner=request.user)
                rd.file.save(f.name, f)
            else:
                url = form.cleaned_data['pdf_url']
                resp = requests.get(url, timeout=30)
                resp.raise_for_status()
                ts = datetime.now().strftime('%Y%m%d_%H%M%S')
                fn = os.path.basename(url) or 'document.pdf'
                rd = RawDocument(url=url, owner=request.user)
                rd.file.save(os.path.join(ts, fn), ContentFile(resp.content))

            rd.save()
            metadata = extract_metadonnees(rd.file.path, rd.url or "")
            text = extract_full_text(rd.file.path)
            
            # Sauvegarder les métadonnées extraites par le LLM dans les champs du modèle
            if metadata:
                rd.title = metadata.get('title', '')
                rd.doc_type = metadata.get('type', '')
                rd.publication_date = metadata.get('publication_date', '')
                rd.version = metadata.get('version', '')
                rd.source = metadata.get('source', '')
                rd.context = metadata.get('context', '')
                rd.country = metadata.get('country', '')
                rd.language = metadata.get('language', '')
                rd.url_source = metadata.get('url_source', rd.url or '')
                rd.save()
                
                print(f"✅ Métadonnées LLM sauvegardées pour le document {rd.pk}")
                print(f"   - Titre: {rd.title}")
                print(f"   - Type: {rd.doc_type}")
                print(f"   - Source: {rd.source}")
                print(f"   - Pays: {rd.country}")

            context.update({
                'doc': rd,
                'metadata': metadata,
                'extracted_text': text
            })
            messages.success(request, "Document importé avec succès!")

        except Exception as e:
            messages.error(request, f"Erreur lors de l'import: {str(e)}")

    return render(request, 'rawdocs/upload.html', context)


@login_required(login_url='rawdocs:login')
@user_passes_test(is_metadonneur)
def document_list(request):
    docs = RawDocument.objects.filter(owner=request.user).order_by('-created_at')
    for d in docs:
        d.basename = os.path.basename(d.file.name)
    return render(request, 'rawdocs/document_list.html', {'documents': docs})


@login_required(login_url='rawdocs:login')
@user_passes_test(is_metadonneur)
def document_metadata(request, doc_id):
    rd = get_object_or_404(RawDocument, id=doc_id, owner=request.user)
    return JsonResponse(extract_metadonnees(rd.file.path, rd.url or ""))


@login_required(login_url='rawdocs:login')
@user_passes_test(is_metadonneur)
def delete_document(request, doc_id):
    rd = get_object_or_404(RawDocument, id=doc_id, owner=request.user)
    if request.method == 'POST':
        rd.delete()
        messages.success(request, "Document supprimé avec succès")
    return redirect('rawdocs:document_list')


@login_required(login_url='rawdocs:login')
@user_passes_test(is_metadonneur)
def edit_metadata(request, doc_id):
    rd = get_object_or_404(RawDocument, id=doc_id, owner=request.user)
    metadata = extract_metadonnees(rd.file.path, rd.url or "")

    if request.method == 'POST':
        form = MetadataEditForm(request.POST)
        if form.is_valid():
            for f, v in form.cleaned_data.items():
                old = metadata.get(f)
                if str(old) != str(v):
                    MetadataLog.objects.create(
                        document=rd, field_name=f,
                        old_value=old, new_value=v,
                        modified_by=request.user
                    )
                    metadata[f] = v
            messages.success(request, "Métadonnées mises à jour")
            return redirect('rawdocs:document_list')
    else:
        form = MetadataEditForm(initial=metadata)

    logs = MetadataLog.objects.filter(document=rd).order_by('-modified_at')
    return render(request, 'rawdocs/edit_metadata.html', {
        'form': form,
        'metadata': metadata,
        'doc': rd,
        'logs': logs
    })


@login_required(login_url='rawdocs:login')
@user_passes_test(is_metadonneur)
def validate_document(request, doc_id):
    document = get_object_or_404(RawDocument, id=doc_id, owner=request.user)

    if request.method == 'POST':
        if not document.pages_extracted:
            try:
                reader = PdfReader(document.file.path)
                pages_text = [page.extract_text() or "" for page in reader.pages]

                with transaction.atomic():
                    for page_num, page_text in enumerate(pages_text, 1):
                        DocumentPage.objects.create(
                            document=document,
                            page_number=page_num,
                            raw_text=page_text,
                            cleaned_text=page_text
                        )

                    document.total_pages = len(pages_text)
                    document.pages_extracted = True

                    # Create standard annotation types
                    types_data = [
                        ('procedure_type', 'Code de Variation', '#3b82f6'),
                        ('authority', 'Autorité', '#8b5cf6'),
                        ('legal_reference', 'Référence Légale', '#f59e0b'),
                        ('required_document', 'Document Requis', '#ef4444'),
                        ('required_condition', 'Condition Requise', '#06b6d4'),
                        ('delay', 'Délai', '#84cc16'),
                    ]

                    for name, display_name, color in types_data:
                        AnnotationType.objects.get_or_create(
                            name=name,
                            defaults={
                                'display_name': display_name,
                                'color': color
                            }
                        )

                    document.is_validated = True
                    document.validated_at = datetime.now()
                    document.save()

                    messages.success(request, f"Document validé ({document.total_pages} pages)")
                    return redirect('rawdocs:document_list')

            except Exception as e:
                messages.error(request, f"Erreur lors de l'extraction: {str(e)}")
                return redirect('rawdocs:document_list')

    return render(request, 'rawdocs/validate_document.html', {'document': document})


# ——— Annotateur Views ——————————————————————————————

@login_required(login_url='rawdocs:login')
@user_passes_test(is_annotateur)
def annotation_dashboard(request):
    docs = RawDocument.objects.filter(
        is_validated=True,
        pages_extracted=True
    ).order_by('-validated_at')

    paginator = Paginator(docs, 10)
    page = request.GET.get('page')

    return render(request, 'rawdocs/annotation_dashboard.html', {
        'documents': paginator.get_page(page)
    })


@login_required(login_url='rawdocs:login')
@user_passes_test(is_annotateur)
def annotate_document(request, doc_id):
    document = get_object_or_404(RawDocument, id=doc_id, is_validated=True)
    pages = document.pages.all()
    pnum = int(request.GET.get('page', 1))
    page_obj = get_object_or_404(DocumentPage, document=document, page_number=pnum)

    return render(request, 'rawdocs/annotate_document.html', {
        'document': document,
        'pages': pages,
        'current_page': page_obj,
        'annotation_types': AnnotationType.objects.all(),
        'existing_annotations': page_obj.annotations.all().order_by('start_pos'),
        'total_pages': document.total_pages
    })


@login_required(login_url='rawdocs:login')
@user_passes_test(is_annotateur)
def save_manual_annotation(request):
    if request.method != 'POST':
        return JsonResponse({'error': 'POST required'}, status=405)

    try:
        data = json.loads(request.body)
        page = get_object_or_404(DocumentPage, id=data['page_id'])
        atype = get_object_or_404(AnnotationType, id=data['type_id'])

        ann = Annotation.objects.create(
            page=page,
            annotation_type=atype,
            start_pos=data['start_pos'],
            end_pos=data['end_pos'],
            selected_text=data['selected_text'],
            confidence_score=100.0,
            created_by=request.user
        )

        return JsonResponse({
            'success': True,
            'annotation_id': ann.id,
            'message': 'Annotation sauvegardée'
        })
    except Exception as e:
        return JsonResponse({
            'error': str(e),
            'message': 'Erreur lors de la sauvegarde'
        }, status=500)


@login_required(login_url='rawdocs:login')
def get_page_annotations(request, page_id):
    page = get_object_or_404(DocumentPage, id=page_id)
    anns = [{
        'id': a.id,
        'start_pos': a.start_pos,
        'end_pos': a.end_pos,
        'selected_text': a.selected_text,
        'type': a.annotation_type.name,
        'type_display': a.annotation_type.display_name,
        'color': a.annotation_type.color,
        'confidence': a.confidence_score,
        'reasoning': a.ai_reasoning,
        'is_validated': a.is_validated,
    } for a in page.annotations.all().order_by('start_pos')]

    return JsonResponse({
        'annotations': anns,
        'page_text': page.cleaned_text
    })


@login_required(login_url='rawdocs:login')
@user_passes_test(is_annotateur)
def delete_annotation(request, annotation_id):
    if request.method != 'POST':
        return JsonResponse({'error': 'POST required'}, status=405)

    ann = get_object_or_404(Annotation, id=annotation_id)
    if ann.created_by != request.user and not request.user.groups.filter(name="Expert").exists():
        return JsonResponse({'error': 'Permission denied'}, status=403)

    ann.delete()
    return JsonResponse({'success': True})


@login_required
@csrf_exempt
def validate_page_annotations(request, page_id):
    """Validate page annotations with RLHF learning"""
    if request.method != 'POST':
        return JsonResponse({'error': 'POST required'}, status=405)

    try:
        page = get_object_or_404(DocumentPage, id=page_id)

        # Get AI annotations from session or reconstruct from DB
        ai_session_key = f'ai_annotations_{page_id}'
        ai_session_data = request.session.get(ai_session_key, [])

        if not ai_session_data:
            ai_session_data = []
            for ann in page.annotations.filter(ai_reasoning__icontains='GROQ'):
                ai_session_data.append({
                    'text': ann.selected_text,
                    'type': ann.annotation_type.name,
                    'start_pos': ann.start_pos,
                    'end_pos': ann.end_pos,
                    'confidence': ann.confidence_score / 100.0
                })

        # Get current annotations (after human edits)
        current_annotations = []
        for annotation in page.annotations.all():
            current_annotations.append({
                'text': annotation.selected_text,
                'type': annotation.annotation_type.name,
                'start_pos': annotation.start_pos,
                'end_pos': annotation.end_pos,
                'confidence': annotation.confidence_score / 100.0
            })

        # Process feedback with RLHF
        rlhf_annotator = RLHFGroqAnnotator()
        feedback_result = rlhf_annotator.process_human_feedback(
            page_id=page_id,
            ai_annotations=ai_session_data,
            human_annotations=current_annotations,
            annotator_id=request.user.id
        )

        # Update page status
        page.is_validated_by_human = True
        page.human_validated_at = datetime.now()
        page.validated_by = request.user
        page.save()

        # Clear session
        if ai_session_key in request.session:
            del request.session[ai_session_key]

        return JsonResponse({
            'success': True,
            'message': f'Page validée! Score: {feedback_result["feedback_score"]:.0%} - IA améliorée!',
            'feedback_score': feedback_result['feedback_score'],
            'corrections_summary': feedback_result['corrections_summary'],
            'ai_improved': True
        })

    except Exception as e:
        print(f"Validation error: {e}")
        return JsonResponse({
            'error': f'Erreur lors de la validation: {str(e)}'
        }, status=500)


@login_required
def get_learning_dashboard(request):
    """Get AI learning metrics dashboard"""
    try:
        # Get recent metrics
        recent_metrics = AILearningMetrics.objects.order_by('-created_at')[:10]

        # Prepare improvement data
        improvement_data = [{
            'date': m.created_at.strftime('%Y-%m-%d'),
            'f1_score': m.f1_score,
            'precision': m.precision_score,
            'recall': m.recall_score
        } for m in recent_metrics]

        # Get feedback stats
        total_feedbacks = AnnotationFeedback.objects.count()
        avg_feedback_score = AnnotationFeedback.objects.aggregate(
            avg_score=models.Avg('feedback_score')
        )['avg_score'] or 0

        # Get entity performance from latest metric
        latest_metric = recent_metrics.first()
        entity_performance = latest_metric.entity_performance if latest_metric else {}

        return JsonResponse({
            'total_feedbacks': total_feedbacks,
            'average_feedback_score': avg_feedback_score,
            'improvement_trend': improvement_data,
            'entity_performance': entity_performance,
            'learning_active': True
        })

    except Exception as e:
        return JsonResponse({'error': str(e)}, status=500)


@login_required
@csrf_exempt
def ai_annotate_page_groq(request, page_id):
    """AI annotation with GROQ and RLHF"""
    if request.method != 'POST':
        return JsonResponse({'error': 'POST required'}, status=405)

    try:
        page = get_object_or_404(DocumentPage, id=page_id)

        # Clear existing annotations
        page.annotations.all().delete()

        # Initialize RLHF annotator
        rlhf_annotator = RLHFGroqAnnotator()

        # Create adaptive prompt and call GROQ
        adaptive_prompt = rlhf_annotator.create_adaptive_prompt(page.cleaned_text)
        response = rlhf_annotator.call_groq_api(adaptive_prompt)

        annotations = rlhf_annotator.parse_groq_response(response, page.page_number) if response else []

        # Store in session for feedback processing
        request.session[f'ai_annotations_{page_id}'] = annotations

        # Save to DB
        saved_count = 0
        for ann_data in annotations:
            try:
                ann_type, _ = AnnotationType.objects.get_or_create(
                    name=ann_data['type'],
                    defaults={
                        'display_name': ann_data['type'].replace('_', ' ').title(),
                        'color': '#3b82f6',
                        'description': f"GROQ detected {ann_data['type']}"
                    }
                )

                Annotation.objects.create(
                    page=page,
                    annotation_type=ann_type,
                    start_pos=ann_data.get('start_pos', 0),
                    end_pos=ann_data.get('end_pos', 0),
                    selected_text=ann_data.get('text', ''),
                    confidence_score=ann_data.get('confidence', 0.8) * 100,
                    ai_reasoning=ann_data.get('reasoning', 'GROQ classification'),
                    created_by=request.user
                )
                saved_count += 1
            except Exception as e:
                print(f"Error saving annotation: {e}")
                continue

        # Update page status
        if saved_count > 0:
            page.is_annotated = True
            page.annotated_at = datetime.now()
            page.annotated_by = request.user
            page.save()

        return JsonResponse({
            'success': True,
            'annotations_created': saved_count,
            'message': f'{saved_count} annotations créées avec GROQ!',
            'learning_enhanced': True
        })

    except Exception as e:
        print(f"GROQ annotation error: {e}")
        return JsonResponse({
            'error': f'Erreur GROQ: {str(e)}'
        }, status=500)


@login_required
def get_document_status(request, doc_id):
    """Get document validation status"""
    try:
        document = get_object_or_404(RawDocument, id=doc_id)
        total_pages = document.pages.count()
        validated_pages = document.pages.filter(is_validated_by_human=True).count()

        return JsonResponse({
            'total_pages': total_pages,
            'validated_pages': validated_pages,
            'is_ready_for_expert': document.is_ready_for_expert,
        })
    except Exception as e:
        return JsonResponse({'error': str(e)}, status=500)


@login_required
@csrf_exempt
def submit_for_expert_review(request, doc_id):
    """Submit entire document for expert review"""
    if request.method != 'POST':
        return JsonResponse({'error': 'POST required'}, status=405)

    try:
        document = get_object_or_404(RawDocument, id=doc_id)
        document.is_ready_for_expert = True
        document.expert_ready_at = datetime.now()
        document.save()

        return JsonResponse({
            'success': True,
            'message': 'Document soumis pour révision expert!'
        })
    except Exception as e:
        return JsonResponse({'error': str(e)}, status=500)


@login_required
@csrf_exempt
def create_annotation_type(request):
    """Create a new annotation type"""
    if request.method != 'POST':
        return JsonResponse({'error': 'POST required'}, status=405)

    try:
        data = json.loads(request.body)
        name = data.get('name', '').strip().lower().replace(' ', '_')
        display_name = data.get('display_name', '').strip()

        if not name or not display_name:
            return JsonResponse({'error': 'Name and display name are required'}, status=400)

        # Check if already exists
        if AnnotationType.objects.filter(name=name).exists():
            return JsonResponse({'error': f'Annotation type "{display_name}" already exists'}, status=400)

        # Create new annotation type
        annotation_type = AnnotationType.objects.create(
            name=name,
            display_name=display_name,
            color='#6366f1',  # Default purple color
            description=f'Custom annotation type created by {request.user.username}'
        )

        return JsonResponse({
            'success': True,
            'annotation_type': {
                'id': annotation_type.id,
                'name': annotation_type.name,
                'display_name': annotation_type.display_name,
                'color': annotation_type.color
            },
            'message': f'Annotation type "{display_name}" created successfully!'
        })

    except Exception as e:
        return JsonResponse({'error': str(e)}, status=500)


@login_required
@csrf_exempt
def delete_annotation_type(request):
    if request.method != 'POST':
        return JsonResponse({'error': 'POST required'}, status=405)

    try:
        data = json.loads(request.body)
        type_id = data.get('type_id')

        if not type_id:
            return JsonResponse({'error': 'Type ID required'}, status=400)

        # Get the annotation type
        annotation_type = get_object_or_404(AnnotationType, id=type_id)

        # Count how many annotations will be deleted
        annotation_count = Annotation.objects.filter(annotation_type=annotation_type).count()

        display_name = annotation_type.display_name

        # FORCE DELETE: Delete all annotations using this type first
        if annotation_count > 0:
            deleted_annotations = Annotation.objects.filter(annotation_type=annotation_type).delete()
            print(f"🗑️ Deleted {annotation_count} annotations of type '{display_name}'")

        # Now delete the annotation type itself
        annotation_type.delete()

        # Create success message
        if annotation_count > 0:
            message = f'Annotation type "{display_name}" and {annotation_count} associated annotation(s) deleted successfully!'
        else:
            message = f'Annotation type "{display_name}" deleted successfully!'

        return JsonResponse({
            'success': True,
            'message': message,
            'deleted_annotations': annotation_count
        })

    except Exception as e:
        print(f"❌ Error deleting annotation type: {e}")
        return JsonResponse({'error': str(e)}, status=500)
    
@login_required
def view_original_document(request, document_id):
    """View the original document PDF - RAWDOCS VERSION"""
    document = get_object_or_404(RawDocument, id=document_id)
    
    # Case 1: Document has a local file
    if document.file:
        try:
            # Serve the PDF file directly in browser
            response = HttpResponse(document.file.read(), content_type='application/pdf')
            response['Content-Disposition'] = f'inline; filename="{document.file.name}"'
            return response
        except Exception as e:
            # If file doesn't exist, show error
            return HttpResponse(
                f"<html><body><h2>Erreur</h2>"
                f"<p>Le fichier PDF n'a pas pu être chargé: {str(e)}</p>"
                f"<script>window.close();</script></body></html>"
            )
    
    # Case 2: Document was uploaded via URL
    elif document.url:
        try:
            # Redirect to the original URL
            return redirect(document.url)
        except Exception as e:
            return HttpResponse(
                f"<html><body><h2>Erreur</h2>"
                f"<p>Impossible d'accéder au document via URL: {str(e)}</p>"
                f"<p><a href='{document.url}' target='_blank'>Essayer d'ouvrir directement: {document.url}</a></p>"
                f"<script>window.close();</script></body></html>"
            )
    
    # Case 3: No file and no URL
    else:
        return HttpResponse(
            "<html><body><h2>Aucun fichier disponible</h2>"
            "<p>Ce document n'a ni fichier PDF ni URL source associé.</p>"
            "<script>window.close();</script></body></html>"
        )
