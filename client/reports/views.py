# client/reports/views.py 
from django.shortcuts import render, get_object_or_404
from django.http import JsonResponse, HttpResponse
from django.utils import timezone
from django.db.models import Count, Avg, Q, Max, Min
from datetime import datetime, timedelta
from django.contrib.auth.decorators import login_required, user_passes_test
from django.contrib.auth.models import User
import json
import csv
import io

# Import from your existing models
from rawdocs.models import RawDocument, DocumentPage, Annotation, AnnotationType
from client.products.models import Product
from expert.models import ExpertLog

def is_client(user):
    return user.groups.filter(name="Client").exists()

@login_required(login_url='rawdocs:login')
@user_passes_test(is_client)
def reports_dashboard(request):
    """Vue principale du dashboard des rapports avec données réelles"""
    
    # Récupération des filtres
    filters = {
        'period': request.GET.get('period', '30d'),
        'product': request.GET.get('product', ''),
        'status': request.GET.get('status', ''),
        'authority': request.GET.get('authority', ''),
    }
    
    # Calcul de la période
    period_days = get_period_days(filters['period'])
    start_date = timezone.now().date() - timedelta(days=period_days)
    
    # KPIs basés sur vos données réelles
    kpis = calculate_real_kpis(start_date, filters)
    
    # Données pour les templates de rapports
    report_templates = get_report_templates()
    
    # Vues sauvegardées simulées
    saved_views = get_saved_views()
    
    # Données pour les graphiques
    chart_data = get_real_chart_data(start_date, filters)
    
    # Données récentes d'activité
    recent_activity = get_recent_activity()
    
    # Filtres disponibles
    available_filters = get_available_filters()
    
    context = {
        'filters': filters,
        'kpis': kpis,
        'report_templates': report_templates,
        'saved_views': saved_views,
        'chart_data': chart_data,
        'recent_activity': recent_activity,
        'available_filters': available_filters,
    }
    
    return render(request, 'client/reports/dashboard.html', context)

def get_period_days(period):
    """Convertir période en nombre de jours"""
    period_map = {
        '7d': 7,
        '30d': 30,
        '90d': 90,
        '1y': 365,
    }
    return period_map.get(period, 30)

def calculate_real_kpis(start_date, filters):
    """Calculer les KPIs basés sur vos données réelles"""
    
    # Documents traités ce mois
    documents_count = RawDocument.objects.filter(
        created_at__gte=start_date,
        is_validated=True
    ).count()
    
    # Annotations créées
    annotations_count = Annotation.objects.filter(
        created_at__gte=start_date
    ).count()
    
    # Produits créés
    products_count = Product.objects.filter(
        created_at__gte=start_date
    ).count()
    
    # Temps moyen de traitement (en jours)
    validated_docs = RawDocument.objects.filter(
        is_validated=True,
        validated_at__isnull=False,
        created_at__gte=start_date
    )
    
    avg_processing_time = 0
    if validated_docs.exists():
        total_time = 0
        count = 0
        for doc in validated_docs:
            if doc.validated_at and doc.created_at:
                processing_time = (doc.validated_at.date() - doc.created_at.date()).days
                total_time += processing_time
                count += 1
        avg_processing_time = total_time / count if count > 0 else 0
    
    return {
        'rapports_mois': documents_count,
        'vues_standard': 3,  # Templates disponibles
        'exports_pdf': annotations_count,  # Annotations comme proxy pour exports
        'partages': products_count,  # Produits créés
        'avg_processing_days': round(avg_processing_time, 1),
        'total_annotations': annotations_count,
        'active_users': User.objects.filter(last_login__gte=start_date).count(),
    }

def get_report_templates():
    """Templates de rapports disponibles"""
    return [
        {
            'name': 'Rapport Mensuel de Conformité',
            'description': 'Vue d\'ensemble des activités réglementaires du mois',
            'type': 'Mensuel',
            'last_generated': '2024-01-15',
            'icon': 'description',
        },
        {
            'name': 'Tableau de Bord KPI',
            'description': 'Indicateurs de performance réglementaire',
            'type': 'Hebdomadaire', 
            'last_generated': '2024-01-12',
            'icon': 'dashboard',
        },
        {
            'name': 'Rapport d\'Audit Réglementaire',
            'description': 'Synthèse des audits et inspections',
            'type': 'Trimestriel',
            'last_generated': '2024-01-08', 
            'icon': 'assessment',
        },
        {
            'name': 'Analyse des Variations',
            'description': 'Suivi des variations de produit et autorités',
            'type': 'Mensuel',
            'last_generated': '2024-01-10',
            'icon': 'trending_up',
        },
    ]

def get_saved_views():
    """Vues sauvegardées"""
    return [
        {
            'name': 'Vue Mensuelle Q4 2024',
            'description': 'Rapport mensuel personnalisé pour Q4',
            'created_at': '2024-01-15',
        },
        {
            'name': 'Rapport Annuel 2024', 
            'description': 'Vue d\'ensemble annuelle complète',
            'created_at': '2024-01-10',
        },
        {
            'name': 'KPI Dashboard Personnalisé',
            'description': 'Indicateurs spécifiques à l\'équipe',
            'created_at': '2024-01-08',
        },
    ]

def get_real_chart_data(start_date, filters):
    """Données réelles pour les graphiques"""
    
    # Documents par jour pour les 30 derniers jours
    daily_docs = []
    for i in range(30):
        date = start_date + timedelta(days=i)
        count = RawDocument.objects.filter(
            created_at__date=date,
            is_validated=True
        ).count()
        daily_docs.append({
            'date': date.strftime('%Y-%m-%d'),
            'count': count
        })
    
    # Répartition par type de document
    doc_types = RawDocument.objects.filter(
        created_at__gte=start_date,
        is_validated=True
    ).values('doc_type').annotate(count=Count('id')).order_by('-count')
    
    # Répartition par autorité
    authorities = Annotation.objects.filter(
        created_at__gte=start_date,
        annotation_type__name='authority'
    ).values('selected_text').annotate(count=Count('id')).order_by('-count')[:5]
    
    return {
        'daily_documents': daily_docs,
        'document_types': list(doc_types),
        'authorities': list(authorities),
    }

def get_recent_activity():
    """Activité récente"""
    recent_docs = RawDocument.objects.filter(
        is_validated=True
    ).order_by('-validated_at')[:10]
    
    recent_products = Product.objects.order_by('-created_at')[:5]
    
    return {
        'recent_documents': recent_docs,
        'recent_products': recent_products,
    }

def get_available_filters():
    """Filtres disponibles pour les dropdowns"""
    
    # Types de documents uniques
    doc_types = RawDocument.objects.values_list('doc_type', flat=True).distinct()
    doc_types = [dt for dt in doc_types if dt]  # Remove empty values
    
    # Autorités depuis les annotations
    authorities = Annotation.objects.filter(
        annotation_type__name='authority'
    ).values_list('selected_text', flat=True).distinct()
    authorities = [auth.strip() for auth in authorities if auth.strip()][:10]
    
    # Pays
    countries = RawDocument.objects.values_list('country', flat=True).distinct()
    countries = [c for c in countries if c]
    
    return {
        'document_types': list(doc_types),
        'authorities': list(authorities),
        'countries': list(countries),
        'periods': [
            ('7d', '7 derniers jours'),
            ('30d', '30 derniers jours'),
            ('90d', '3 derniers mois'),
            ('1y', 'Année courante'),
        ]
    }

@login_required(login_url='rawdocs:login')
@user_passes_test(is_client)
def generate_report(request):
    """Générer un rapport basé sur les filtres"""
    if request.method == 'POST':
        try:
            data = json.loads(request.body)
            template = data.get('template')
            period = data.get('period')
            authority = data.get('authority')
            
            # Logique de génération de rapport
            report_data = {
                'template': template,
                'generated_at': timezone.now().isoformat(),
                'period': period,
                'authority': authority,
                'status': 'success'
            }
            
            return JsonResponse(report_data)
            
        except Exception as e:
            return JsonResponse({'error': str(e)}, status=400)
    
    return JsonResponse({'error': 'POST required'}, status=405)

@login_required(login_url='rawdocs:login') 
@user_passes_test(is_client)
def export_data(request):
    """Export des données en CSV/PDF"""
    format_type = request.GET.get('format', 'csv')
    
    if format_type == 'csv':
        # Export CSV des documents récents
        response = HttpResponse(content_type='text/csv')
        response['Content-Disposition'] = 'attachment; filename="regx_report.csv"'
        
        writer = csv.writer(response)
        writer.writerow(['Document', 'Type', 'Status', 'Date', 'Owner'])
        
        documents = RawDocument.objects.filter(is_validated=True)[:100]
        for doc in documents:
            writer.writerow([
                f'Document #{doc.id}',
                doc.doc_type or 'N/A',
                'Validé' if doc.is_validated else 'En attente',
                doc.created_at.strftime('%Y-%m-%d'),
                doc.owner.username if doc.owner else 'N/A'
            ])
        
        return response
    
    return JsonResponse({'error': 'Format not supported'}, status=400)

# Placeholder views pour les autres endpoints
def submission_detail(request, pk):
    return JsonResponse({'status': 'success', 'message': 'Detail view coming soon'})

def reports_settings(request):
    return render(request, 'client/reports/settings.html', {'message': 'Settings page'})

def reports_create(request):
    return render(request, 'client/reports/create.html', {'message': 'Create page'})