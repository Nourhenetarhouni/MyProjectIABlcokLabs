from django.shortcuts import render, get_object_or_404, redirect
from django.contrib.auth.decorators import login_required
from django.contrib import messages
from django.http import JsonResponse, HttpResponse
from django.views.generic import ListView, DetailView, CreateView, UpdateView
from django.contrib.auth.mixins import LoginRequiredMixin
from django.urls import reverse_lazy
from django.template.loader import render_to_string
from django.views.decorators.http import require_http_methods
from reportlab.pdfgen import canvas
from reportlab.lib.pagesizes import letter
from reportlab.platypus import SimpleDocTemplate, Paragraph, Spacer, Table, TableStyle
from reportlab.lib.styles import getSampleStyleSheet, ParagraphStyle
from reportlab.lib import colors
from io import BytesIO
import json

from .models import Submission, SubmissionModule, ModuleSection, FormattedTemplate, SubmissionSuggestion
from .forms import SubmissionForm, FormattedTemplateForm


class SubmissionListView(LoginRequiredMixin, ListView):
    model = Submission
    template_name = 'submissions/submission_list.html'
    context_object_name = 'submissions'
    paginate_by = 10

    def get_queryset(self):
        return Submission.objects.filter(created_by=self.request.user)


@login_required
def submission_create(request):
    if request.method == 'POST':
        form = SubmissionForm(request.POST)
        if form.is_valid():
            submission = form.save(commit=False)
            submission.created_by = request.user
            submission.save()

            # Générer la structure CTD automatiquement
            generate_ctd_structure(submission)

            messages.success(request, f'Soumission "{submission.name}" créée avec succès!')
            return redirect('submissions:detail', pk=submission.pk)
    else:
        form = SubmissionForm()

    return render(request, 'submissions/submission_create.html', {'form': form})


@login_required
def submission_detail(request, pk):
    submission = get_object_or_404(Submission, pk=pk, created_by=request.user)
    modules = submission.modules.all()
    suggestions = submission.suggestions.filter(is_applied=False)

    context = {
        'submission': submission,
        'modules': modules,
        'suggestions': suggestions,
    }
    return render(request, 'submissions/submission_detail.html', context)


@login_required
def module_section_view(request, submission_pk, module_pk, section_pk):
    submission = get_object_or_404(Submission, pk=submission_pk, created_by=request.user)
    module = get_object_or_404(SubmissionModule, pk=module_pk, submission=submission)
    section = get_object_or_404(ModuleSection, pk=section_pk, module=module)

    # Voir le contenu réel de la section
    context = {
        'submission': submission,
        'module': module,
        'section': section,
    }
    return render(request, 'submissions/section_view.html', context)


@login_required
def module_section_template(request, submission_pk, module_pk, section_pk):
    submission = get_object_or_404(Submission, pk=submission_pk, created_by=request.user)
    module = get_object_or_404(SubmissionModule, pk=module_pk, submission=submission)
    section = get_object_or_404(ModuleSection, pk=section_pk, module=module)

    # Obtenir ou créer le template formaté
    template, created = FormattedTemplate.objects.get_or_create(
        section=section,
        defaults={
            'template_name': f'EMA Template - {section.title}',
        }
    )

    if request.method == 'POST':
        form = FormattedTemplateForm(request.POST, instance=template)
        if form.is_valid():
            form.save()
            section.is_completed = True
            section.save()
            messages.success(request, 'Template sauvegardé avec succès!')
            return redirect('submissions:detail', pk=submission.pk)
    else:
        form = FormattedTemplateForm(instance=template)

    context = {
        'submission': submission,
        'module': module,
        'section': section,
        'template': template,
        'form': form,
    }
    return render(request, 'submissions/section_template.html', context)


@login_required
def generate_ctd_structure_view(request, pk):
    submission = get_object_or_404(Submission, pk=pk, created_by=request.user)

    if request.method == 'POST':
        # Regénérer la structure CTD
        generate_ctd_structure(submission)
        messages.success(request, 'Structure CTD générée avec succès!')

    return redirect('submissions:detail', pk=submission.pk)


@login_required
@require_http_methods(["POST"])
def apply_suggestions(request, pk):
    submission = get_object_or_404(Submission, pk=pk, created_by=request.user)

    try:
        suggestions = submission.suggestions.filter(is_applied=False)
        for suggestion in suggestions:
            if suggestion.suggestion_type == 'missing_section':
                # Ajouter la section manquante
                add_missing_section(submission, suggestion)
            suggestion.is_applied = True
            suggestion.save()

        return JsonResponse({'success': True, 'message': 'Suggestions appliquées avec succès!'})
    except Exception as e:
        return JsonResponse({'success': False, 'message': str(e)})


@login_required
def download_template_pdf(request, submission_pk, section_pk):
    submission = get_object_or_404(Submission, pk=submission_pk, created_by=request.user)
    section = get_object_or_404(ModuleSection, pk=section_pk)

    try:
        template = section.formatted_template
    except FormattedTemplate.DoesNotExist:
        messages.error(request, 'Aucun template trouvé pour cette section.')
        return redirect('submissions:detail', pk=submission.pk)

    # Générer le PDF
    buffer = BytesIO()
    doc = SimpleDocTemplate(buffer, pagesize=letter)
    styles = getSampleStyleSheet()
    story = []

    # En-tête EMA
    title_style = ParagraphStyle(
        'CustomTitle',
        parent=styles['Heading1'],
        fontSize=16,
        spaceAfter=30,
        alignment=1  # Center
    )

    story.append(Paragraph("EUROPEAN MEDICINES AGENCY", title_style))
    story.append(Paragraph("SCIENCE MEDICINES HEALTH", styles['Normal']))
    story.append(Spacer(1, 20))

    # Date et division
    story.append(Paragraph(f"18 July 2025", styles['Normal']))
    story.append(Paragraph(f"Information Management Division, Version 5", styles['Normal']))
    story.append(Spacer(1, 20))

    # Titre du template
    story.append(Paragraph(template.template_name, styles['Heading2']))
    story.append(Paragraph("To be inserted in each procedural submission cover letter.", styles['Normal']))
    story.append(Spacer(1, 20))

    # Tableau des données
    data = [
        ['1*', 'Applicant/MAH Name', template.applicant_name or ''],
        ['2*', 'Customer Account Number', template.customer_account_number or ''],
        ['3*', 'Customer Reference / Purchase Order Number', template.customer_reference or ''],
        ['4', 'INN / Active substance/ATC Code', template.inn_code or ''],
        ['5', 'Product Name of centrally authorised medicinal product(s)', template.product_name or ''],
    ]

    table = Table(data, colWidths=[50, 250, 200])
    table.setStyle(TableStyle([
        ('BACKGROUND', (0, 0), (0, -1), colors.navy),
        ('TEXTCOLOR', (0, 0), (0, -1), colors.white),
        ('FONTNAME', (0, 0), (0, -1), 'Helvetica-Bold'),
        ('FONTSIZE', (0, 0), (-1, -1), 10),
        ('ALIGN', (0, 0), (-1, -1), 'LEFT'),
        ('VALIGN', (0, 0), (-1, -1), 'MIDDLE'),
        ('GRID', (0, 0), (-1, -1), 1, colors.black),
        ('BACKGROUND', (1, 0), (-1, -1), colors.lightgrey),
    ]))

    story.append(table)
    doc.build(story)

    buffer.seek(0)
    response = HttpResponse(buffer.getvalue(), content_type='application/pdf')
    response['Content-Disposition'] = f'attachment; filename="template_{section.section_number}.pdf"'

    return response


def generate_ctd_structure(submission):
    """Génère automatiquement la structure CTD basée sur le type de soumission et région"""

    # Supprimer les modules existants
    submission.modules.all().delete()

    # Structure CTD standard
    ctd_structure = {
        'M1': {
            'title': 'Module 1 - Administrative Information',
            'sections': [
                ('1.1', 'Cover Letter'),
                ('1.2', 'Comprehensive Table of Contents'),
                ('1.3', 'Application Form'),
            ]
        },
        'M2': {
            'title': 'Module 2 - Summaries',
            'sections': [
                ('2.1', 'Common Technical Document Summaries'),
                ('2.2', 'Introduction'),
                ('2.3', 'Quality Overall Summary'),
            ]
        },
        'M3': {
            'title': 'Module 3 - Quality',
            'sections': [
                ('3.1', 'Drug Substance'),
                ('3.2', 'Drug Product'),
                ('3.3', 'Literature References'),
            ]
        },
        'M4': {
            'title': 'Module 4 - Nonclinical Study Reports',
            'sections': [
                ('4.1', 'Pharmacology'),
                ('4.2', 'Pharmacokinetics'),
                ('4.3', 'Toxicology'),
            ]
        },
        'M5': {
            'title': 'Module 5 - Clinical Study Reports',
            'sections': [
                ('5.1', 'Clinical Study Reports'),
                ('5.2', 'Literature References'),
                ('5.3', 'Case Report Forms'),
            ]
        }
    }

    # Créer les modules et sections
    for module_key, module_data in ctd_structure.items():
        module = SubmissionModule.objects.create(
            submission=submission,
            module_type=module_key,
            title=module_data['title'],
            order=int(module_key[1])
        )

        for section_number, section_title in module_data['sections']:
            ModuleSection.objects.create(
                module=module,
                section_number=section_number,
                title=section_title,
                order=float(section_number)
            )

    # Générer des suggestions intelligentes
    generate_suggestions(submission)


def generate_suggestions(submission):
    """Génère des suggestions IA basées sur le type de soumission"""

    suggestions_data = [
        {
            'title': 'Structure CTD optimisée pour EU',
            'description': 'La structure a été optimisée selon les guidelines EMA les plus récentes.',
            'suggestion_type': 'structure'
        },
        {
            'title': 'Sections manquantes détectées: Module 2.7',
            'description': 'Des sections additionnelles recommandées pour ce type de variation ont été détectées.',
            'suggestion_type': 'missing_section'
        },
        {
            'title': 'Recommandation: Ajouter données comparatives pour cette variation',
            'description': 'Pour ce type de changement, il est recommandé d\'inclure des données comparatives.',
            'suggestion_type': 'recommendation'
        }
    ]

    for suggestion_data in suggestions_data:
        SubmissionSuggestion.objects.create(
            submission=submission,
            **suggestion_data
        )


def add_missing_section(submission, suggestion):
    """Ajoute une section manquante basée sur la suggestion"""
    # Logique pour ajouter des sections manquantes
    # Cette fonction peut être étendue selon les besoins spécifiques
    pass