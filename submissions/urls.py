from django.urls import path
from . import views

app_name = 'submissions'

urlpatterns = [
    # Liste des soumissions
    path('', views.SubmissionListView.as_view(), name='list'),

    # Créer une nouvelle soumission
    path('create/', views.submission_create, name='create'),

    # Détail d'une soumission
    path('<int:pk>/', views.submission_detail, name='detail'),

    # Générer structure CTD
    path('<int:pk>/generate-structure/', views.generate_ctd_structure_view, name='generate_structure'),

    # Appliquer les suggestions
    path('<int:pk>/apply-suggestions/', views.apply_suggestions, name='apply_suggestions'),

    # Voir une section (bouton "Voir")
    path('<int:submission_pk>/module/<int:module_pk>/section/<int:section_pk>/view/',
         views.module_section_view, name='section_view'),

    # Template d'une section (bouton "Template")
    path('<int:submission_pk>/module/<int:module_pk>/section/<int:section_pk>/template/',
         views.module_section_template, name='section_template'),

    # Télécharger le template en PDF
    path('<int:submission_pk>/section/<int:section_pk>/download-pdf/',
         views.download_template_pdf, name='download_template_pdf'),
]