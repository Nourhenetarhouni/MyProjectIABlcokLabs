from django.shortcuts import render, get_object_or_404, redirect
from django.http import JsonResponse, HttpResponse, Http404
from django.views.decorators.csrf import csrf_exempt
from django.views.decorators.http import require_http_methods
from django.db.models import Q, Count
from django.core.paginator import Paginator
from django.contrib import messages
from django.utils import timezone
from rest_framework import generics, status
from rest_framework.decorators import api_view
from rest_framework.response import Response
from client.library.models import Document, DocumentCategory, RegulatoryAuthority, DocumentTranslation
# Import des modèles RawDocument pour la bibliothèque
from rawdocs.models import RawDocument
import json
import logging
import os

logger = logging.getLogger(__name__)

from django.shortcuts import render, get_object_or_404, redirect
from django.http import JsonResponse, HttpResponse, Http404
from django.views.decorators.csrf import csrf_exempt
from django.views.decorators.http import require_http_methods
from django.db.models import Q, Count
from django.core.paginator import Paginator
from django.contrib import messages
from django.utils import timezone
from django.core.cache import cache
from rest_framework import generics, status
from rest_framework.decorators import api_view
from rest_framework.response import Response
from client.library.models import Document, DocumentCategory, RegulatoryAuthority, DocumentTranslation
# Import des modèles RawDocument pour la bibliothèque
from rawdocs.models import RawDocument
import json
import logging
import os

logger = logging.getLogger(__name__)

def library_dashboard(request):
    """Vue principale de la library - affiche les documents des métadonneurs"""
    # Utiliser le cache pour les statistiques avec timeout de 5 minutes
    total_documents = cache.get('total_documents')
    if total_documents is None:
        total_documents = RawDocument.objects.filter(is_validated=True).count()
        cache.set('total_documents', total_documents, 300)  # 5 minutes
    
    pending_validation = RawDocument.objects.filter(is_validated=False).count()
    total_metadonneurs = RawDocument.objects.values('owner').distinct().count()
    
    # Documents récents validés avec métadonnées
    recent_documents = RawDocument.objects.filter(
        is_validated=True
    ).select_related('owner').order_by('-created_at')[:10]
    
    # Statistiques par type de document avec cache
    document_type_stats = cache.get('document_type_stats')
    if document_type_stats is None:
        document_type_stats = RawDocument.objects.filter(
            is_validated=True
        ).exclude(doc_type='').values('doc_type').annotate(
            count=Count('id')
        ).order_by('-count')[:5]
        cache.set('document_type_stats', document_type_stats, 300)
    
    # Statistiques par pays avec cache
    country_stats = cache.get('country_stats') 
    if country_stats is None:
        country_stats = RawDocument.objects.filter(
            is_validated=True
        ).exclude(country='').values('country').annotate(
            count=Count('id')
        ).order_by('-count')[:5]
        cache.set('country_stats', country_stats, 300)
    
    # 🆕 Statistiques par source avec catégories personnalisées avec cache
    source_categories = cache.get('source_categories')
    if source_categories is None:
        source_stats = RawDocument.objects.filter(
            is_validated=True
        ).exclude(source='').values('source').annotate(
            count=Count('id')
        ).order_by('-count')
        
        # Créer des catégories basées sur les sources
        categories = {}
        neutral_count = 0
        
        for stat in source_stats:
            source_name = stat['source'].upper()
            count = stat['count']
            
            # Mapper les sources aux catégories connues
            if 'EMA' in source_name or 'EUROPEAN' in source_name:
                if 'EMA' not in categories:
                    categories['EMA'] = {'name': 'EMA', 'count': 0, 'color': '#3498db'}
                categories['EMA']['count'] += count
            elif 'FDA' in source_name:
                if 'FDA' not in categories:
                    categories['FDA'] = {'name': 'FDA', 'count': 0, 'color': '#e74c3c'}
                categories['FDA']['count'] += count
            elif 'ICH' in source_name:
                if 'ICH' not in categories:
                    categories['ICH'] = {'name': 'ICH', 'count': 0, 'color': '#f39c12'}
                categories['ICH']['count'] += count
            elif 'ANSM' in source_name:
                if 'ANSM' not in categories:
                    categories['ANSM'] = {'name': 'ANSM', 'count': 0, 'color': '#2ecc71'}
                categories['ANSM']['count'] += count
            elif 'MHRA' in source_name:
                if 'MHRA' not in categories:
                    categories['MHRA'] = {'name': 'MHRA', 'count': 0, 'color': '#9b59b6'}
                categories['MHRA']['count'] += count
            else:
                neutral_count += count
        
        # Ajouter la catégorie Neutre si nécessaire
        if neutral_count > 0:
            categories['NEUTRE'] = {'name': 'Neutre', 'count': neutral_count, 'color': '#95a5a6'}
        
        source_categories = categories
        cache.set('source_categories', source_categories, 300)
    
    context = {
        'total_documents': total_documents,
        'pending_validation': pending_validation, 
        'total_metadonneurs': total_metadonneurs,
        'recent_documents': recent_documents,
        'document_type_stats': document_type_stats,
        'country_stats': country_stats,
        'source_categories': source_categories,  # 🆕 Nouvelles catégories par source
    }
    
    return render(request, 'client/library/dashboard.html', context)

def document_list(request):
    """Liste des documents RawDocument avec filtrage"""
    # Paramètres de filtrage
    search = request.GET.get('search', '')
    document_type = request.GET.get('type', '')
    country = request.GET.get('country', '')
    language = request.GET.get('language', '')
    validation_status = request.GET.get('status', 'validated')
    
    # Construction de la requête sur RawDocument
    documents_qs = RawDocument.objects.select_related('owner').all()
    
    # Filtrer seulement les documents validés par défaut
    if validation_status == 'validated':
        documents_qs = documents_qs.filter(is_validated=True)
    elif validation_status == 'pending':
        documents_qs = documents_qs.filter(is_validated=False)
    
    if search:
        documents_qs = documents_qs.filter(
            Q(title__icontains=search) | 
            Q(source__icontains=search) |
            Q(context__icontains=search)
        )
    
    if document_type:
        documents_qs = documents_qs.filter(doc_type__icontains=document_type)
    
    if country:
        documents_qs = documents_qs.filter(country__icontains=country)
    
    if language:
        documents_qs = documents_qs.filter(language__icontains=language)
    
    documents_qs = documents_qs.order_by('-created_at')
    
    # Pagination
    paginator = Paginator(documents_qs, 20)
    page_number = request.GET.get('page')
    documents = paginator.get_page(page_number)
    
    # Options de filtrage basées sur RawDocument
    document_types = RawDocument.objects.filter(is_validated=True).exclude(doc_type='').values_list('doc_type', flat=True).distinct()
    countries = RawDocument.objects.filter(is_validated=True).exclude(country='').values_list('country', flat=True).distinct()
    languages = RawDocument.objects.filter(is_validated=True).exclude(language='').values_list('language', flat=True).distinct()
    
    context = {
        'documents': documents,
        'document_types': document_types,
        'countries': countries,
        'languages': languages,
        'filters': {
            'search': search,
            'type': document_type,
            'country': country,
            'language': language,
            'status': validation_status,
        }
    }
    
    return render(request, 'client/library/document_list.html', context)

def documents_by_category(request, category):
    """Documents filtrés par catégorie de source"""
    # Définir les filtres de source par catégorie
    source_filters = {
        'ema': ['EMA', 'EUROPEAN', 'European Medicines Agency'],
        'fda': ['FDA', 'Food and Drug Administration'],
        'ich': ['ICH', 'International Council for Harmonisation'],
        'ansm': ['ANSM', 'Agence nationale de sécurité du médicament'],
        'mhra': ['MHRA', 'Medicines and Healthcare products Regulatory Agency'],
        'neutre': []  # Pour les autres sources
    }
    
    category_lower = category.lower()
    documents_qs = RawDocument.objects.filter(is_validated=True).select_related('owner')
    
    if category_lower in source_filters and source_filters[category_lower]:
        # Filtrer par sources spécifiques
        source_query = Q()
        for source_pattern in source_filters[category_lower]:
            source_query |= Q(source__icontains=source_pattern)
        documents_qs = documents_qs.filter(source_query)
    elif category_lower == 'neutre':
        # Exclure toutes les sources connues
        exclude_query = Q()
        for source_list in source_filters.values():
            if source_list:  # Ignorer la liste vide pour 'neutre'
                for pattern in source_list:
                    exclude_query |= Q(source__icontains=pattern)
        documents_qs = documents_qs.exclude(exclude_query)
    
    documents_qs = documents_qs.order_by('-created_at')
    
    # Pagination
    paginator = Paginator(documents_qs, 20)
    page_number = request.GET.get('page')
    documents = paginator.get_page(page_number)
    
    context = {
        'documents': documents,
        'category': category.upper(),
        'category_display': {
            'ema': 'EMA - European Medicines Agency',
            'fda': 'FDA - Food and Drug Administration', 
            'ich': 'ICH - International Council for Harmonisation',
            'ansm': 'ANSM - Agence nationale de sécurité du médicament',
            'mhra': 'MHRA - Medicines and Healthcare products Regulatory Agency',
            'neutre': 'Documents - Sources Diverses'
        }.get(category_lower, category.upper()),
    }
    
    return render(request, 'client/library/documents_by_category.html', context)

def document_list_horizontal(request):
    """Liste horizontale des documents avec noms et données principales"""
    # Paramètres de filtrage
    search = request.GET.get('search', '')
    document_type = request.GET.get('type', '')
    country = request.GET.get('country', '')
    language = request.GET.get('language', '')
    
    # Construction de la requête sur RawDocument
    documents_qs = RawDocument.objects.filter(is_validated=True).select_related('owner')
    
    if search:
        documents_qs = documents_qs.filter(
            Q(title__icontains=search) | 
            Q(source__icontains=search) |
            Q(context__icontains=search)
        )
    
    if document_type:
        documents_qs = documents_qs.filter(doc_type__icontains=document_type)
    
    if country:
        documents_qs = documents_qs.filter(country__icontains=country)
    
    if language:
        documents_qs = documents_qs.filter(language__icontains=language)
    
    documents_qs = documents_qs.order_by('-created_at')
    
    # Pagination
    paginator = Paginator(documents_qs, 50)  # Plus de documents pour la vue horizontale
    page_number = request.GET.get('page')
    documents = paginator.get_page(page_number)
    
    # Options de filtrage
    document_types = RawDocument.objects.filter(is_validated=True).exclude(doc_type='').values_list('doc_type', flat=True).distinct()
    countries = RawDocument.objects.filter(is_validated=True).exclude(country='').values_list('country', flat=True).distinct()
    languages = RawDocument.objects.filter(is_validated=True).exclude(language='').values_list('language', flat=True).distinct()
    
    context = {
        'documents': documents,
        'document_types': document_types,
        'countries': countries,
        'languages': languages,
        'filters': {
            'search': search,
            'type': document_type,
            'country': country,
            'language': language,
        }
    }
    
    return render(request, 'client/library/document_list_horizontal.html', context)

def documents_by_type(request, doc_type):
    """Documents filtrés par type avec affichage horizontal"""
    # Paramètres de filtrage additionnels
    search = request.GET.get('search', '')
    country = request.GET.get('country', '')
    language = request.GET.get('language', '')
    
    # Construction de la requête sur RawDocument
    documents_qs = RawDocument.objects.filter(
        is_validated=True,
        doc_type__icontains=doc_type
    ).select_related('owner')
    
    if search:
        documents_qs = documents_qs.filter(
            Q(title__icontains=search) | 
            Q(source__icontains=search) |
            Q(context__icontains=search)
        )
    
    if country:
        documents_qs = documents_qs.filter(country__icontains=country)
    
    if language:
        documents_qs = documents_qs.filter(language__icontains=language)
    
    documents_qs = documents_qs.order_by('-created_at')
    
    # Pagination
    paginator = Paginator(documents_qs, 50)
    page_number = request.GET.get('page')
    documents = paginator.get_page(page_number)
    
    # Options de filtrage
    countries = RawDocument.objects.filter(is_validated=True).exclude(country='').values_list('country', flat=True).distinct()
    languages = RawDocument.objects.filter(is_validated=True).exclude(language='').values_list('language', flat=True).distinct()
    
    context = {
        'documents': documents,
        'doc_type': doc_type,
        'countries': countries,
        'languages': languages,
        'filters': {
            'search': search,
            'country': country,
            'language': language,
        }
    }
    
    return render(request, 'client/library/documents_by_type.html', context)

def documents_by_country(request, country):
    """Documents filtrés par pays avec affichage horizontal"""
    # Paramètres de filtrage additionnels
    search = request.GET.get('search', '')
    document_type = request.GET.get('type', '')
    language = request.GET.get('language', '')
    
    # Construction de la requête sur RawDocument
    documents_qs = RawDocument.objects.filter(
        is_validated=True,
        country__icontains=country
    ).select_related('owner')
    
    if search:
        documents_qs = documents_qs.filter(
            Q(title__icontains=search) | 
            Q(source__icontains=search) |
            Q(context__icontains=search)
        )
    
    if document_type:
        documents_qs = documents_qs.filter(doc_type__icontains=document_type)
    
    if language:
        documents_qs = documents_qs.filter(language__icontains=language)
    
    documents_qs = documents_qs.order_by('-created_at')
    
    # Pagination
    paginator = Paginator(documents_qs, 50)
    page_number = request.GET.get('page')
    documents = paginator.get_page(page_number)
    
    # Options de filtrage
    document_types = RawDocument.objects.filter(is_validated=True).exclude(doc_type='').values_list('doc_type', flat=True).distinct()
    languages = RawDocument.objects.filter(is_validated=True).exclude(language='').values_list('language', flat=True).distinct()
    
    context = {
        'documents': documents,
        'country': country,
        'document_types': document_types,
        'languages': languages,
        'filters': {
            'search': search,
            'type': document_type,
            'language': language,
        }
    }
    
    return render(request, 'client/library/documents_by_country.html', context)

def document_detail(request, pk):
    """Détail d'un RawDocument avec ses métadonnées extraites par les métadonneurs"""
    document = get_object_or_404(RawDocument, pk=pk, is_validated=True)
    
    # Utiliser directement les métadonnées extraites par les métadonneurs
    # stockées dans les champs du modèle RawDocument
    metadata = {
        'title': document.title or 'Non spécifié',
        'doc_type': document.doc_type or 'Non spécifié', 
        'publication_date': document.publication_date or 'Non spécifiée',
        'version': document.version or 'Non spécifiée',
        'source': document.source or 'Non spécifiée',
        'context': document.context or 'Non spécifié',
        'country': document.country or 'Non spécifié',
        'language': document.language or 'Non spécifiée',
        'url_source': document.url_source or document.url or 'Non spécifiée',
        'owner': document.owner.username if document.owner else 'Non spécifié',
        'created_at': document.created_at,
        'is_validated': document.is_validated,
        'validated_at': document.validated_at,
        'total_pages': document.total_pages,
        'pages_extracted': document.pages_extracted,
        'is_ready_for_expert': document.is_ready_for_expert,
        'expert_ready_at': document.expert_ready_at,
    }
    
    # Documents similaires (même type et pays)
    related_documents = RawDocument.objects.filter(
        doc_type=document.doc_type,
        country=document.country,
        is_validated=True
    ).exclude(pk=document.pk)[:5]
    
    context = {
        'document': document,
        'metadata': metadata,
        'related_documents': related_documents,
    }
    
    return render(request, 'client/library/document_detail.html', context)

def download_document(request, pk):
    """Télécharger un RawDocument"""
    document = get_object_or_404(RawDocument, pk=pk, is_validated=True)
    
    if not document.file:
        raise Http404("Fichier non trouvé")
    
    # Retourner le fichier
    response = HttpResponse(document.file.read(), content_type='application/pdf')
    filename = document.file.name.split('/')[-1]
    response['Content-Disposition'] = f'attachment; filename="{filename}"'
    return response

@api_view(['GET'])
def search_documents(request):
    """API de recherche de documents"""
    query = request.GET.get('q', '')
    limit = int(request.GET.get('limit', 10))
    
    if not query:
        return Response([])
    
    documents = Document.objects.filter(
        Q(title__icontains=query) | 
        Q(description__icontains=query) |
        Q(tags__icontains=query),
        validation_status='validated'
    ).select_related('authority', 'category')[:limit]
    
    results = []
    for doc in documents:
        results.append({
            'id': doc.id,
            'title': doc.title,
            'authority': doc.authority.name,
            'type': doc.get_document_type_display(),
            'publication_date': doc.publication_date.isoformat() if doc.publication_date else None,
            'url': doc.get_absolute_url()
        })
    
    return Response(results)

@api_view(['GET'])
def document_metadata(request, pk):
    """API pour récupérer les métadonnées d'un document"""
    document = get_object_or_404(Document, pk=pk)
    
    metadata = {
        'id': document.id,
        'title': document.title,
        'description': document.description,
        'document_type': document.get_document_type_display(),
        'authority': {
            'name': document.authority.name,
            'code': document.authority.code,
            'country': document.authority.country,
        },
        'category': document.category.name if document.category else None,
        'language': document.get_language_display(),
        'publication_date': document.publication_date.isoformat() if document.publication_date else None,
        'effective_date': document.effective_date.isoformat() if document.effective_date else None,
        'expiry_date': document.expiry_date.isoformat() if document.expiry_date else None,
        'reference_number': document.reference_number,
        'source_url': document.source_url,
        'tags': document.tags_list,
        'ctd_section': document.ctd_section,
        'therapeutic_area': document.therapeutic_area,
        'file_size': document.formatted_file_size,
        'file_extension': document.file_extension,
        'validation_status': document.get_validation_status_display(),
        'validated_by': document.validated_by,
        'validation_date': document.validation_date.isoformat() if document.validation_date else None,
        'view_count': document.view_count,
        'download_count': document.download_count,
        'created_at': document.created_at.isoformat(),
        'updated_at': document.updated_at.isoformat(),
    }
    
    return Response(metadata)

def upload_document(request):
    """Interface d'upload de document avec traitement du formulaire"""
    if request.method == 'POST':
        try:
            # Récupération des données du formulaire
            file = request.FILES.get('file')
            title = request.POST.get('title', '').strip()
            description = request.POST.get('description', '').strip()
            document_type = request.POST.get('document_type')
            language = request.POST.get('language')
            authority_id = request.POST.get('authority')
            category_id = request.POST.get('category')
            reference_number = request.POST.get('reference_number', '').strip()
            source_url = request.POST.get('source_url', '').strip()
            publication_date = request.POST.get('publication_date')
            effective_date = request.POST.get('effective_date')
            expiry_date = request.POST.get('expiry_date')
            ctd_section = request.POST.get('ctd_section', '').strip()
            therapeutic_area = request.POST.get('therapeutic_area', '').strip()
            tags = request.POST.get('tags', '').strip()
            validated_by = request.POST.get('validated_by', 'RegX Admin').strip()
            validation_notes = request.POST.get('validation_notes', '').strip()

            # Validation des champs obligatoires
            if not all([file, title, document_type, language, authority_id, publication_date]):
                messages.error(request, "Veuillez remplir tous les champs obligatoires.")
                return redirect('library:upload_document')

            # Récupération des objets liés
            try:
                authority = RegulatoryAuthority.objects.get(id=authority_id)
            except RegulatoryAuthority.DoesNotExist:
                messages.error(request, "Autorité réglementaire invalide.")
                return redirect('library:upload_document')

            category = None
            if category_id:
                try:
                    category = DocumentCategory.objects.get(id=category_id)
                except DocumentCategory.DoesNotExist:
                    pass

            # Calcul de la taille du fichier
            file_size = file.size if file else 0

            # Création du document
            document = Document.objects.create(
                title=title,
                description=description,
                document_type=document_type,
                category=category,
                authority=authority,
                source_url=source_url,
                reference_number=reference_number,
                file=file,
                file_size=file_size,
                language=language,
                publication_date=publication_date,
                effective_date=effective_date if effective_date else None,
                expiry_date=expiry_date if expiry_date else None,
                validation_status='validated',  # Auto-validation pour le MVP
                validated_by=validated_by,
                validation_date=timezone.now(),
                validation_notes=validation_notes,
                tags=tags,
                ctd_section=ctd_section,
                therapeutic_area=therapeutic_area,
                created_by=validated_by,
            )

            logger.info(f"Document '{title}' uploaded successfully with ID {document.id}")
            messages.success(request, f"Document '{title}' a été uploadé avec succès!")
            
            return redirect('library:document_detail', pk=document.id)

        except Exception as e:
            logger.error(f"Error uploading document: {e}")
            messages.error(request, f"Erreur lors de l'upload du document: {str(e)}")
            return redirect('library:upload_document')
    
    # GET request - afficher le formulaire
    authorities = RegulatoryAuthority.objects.all().order_by('name')
    categories = DocumentCategory.objects.all().order_by('name')
    
    context = {
        'authorities': authorities,
        'categories': categories,
        'document_types': Document.DOCUMENT_TYPES,
        'languages': Document.LANGUAGES,
    }
    
    return render(request, 'client/library/upload_document.html', context)
