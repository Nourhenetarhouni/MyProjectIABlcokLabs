from django.urls import path
from django.contrib.auth import views as auth_views
from . import views

app_name = 'rawdocs'

urlpatterns = [
    # 1) Page d'accueil → login avec redirection personnalisée
    path(
        '',
        views.CustomLoginView.as_view(),
        name='login'
    ),

    # 2) Déconnexion
    path(
        'logout/',
        auth_views.LogoutView.as_view(next_page='rawdocs:login'),
        name='logout'
    ),

    # 3) Inscription
    path(
        'register/',
        views.register,
        name='register'
    ),

    # 4) Upload (Métadonneur) — URL ou fichier local
    path(
        'upload/',
        views.upload_pdf,
        name='upload'
    ),

    # 5) Liste des documents importés
    path(
        'documents/',
        views.document_list,
        name='document_list'
    ),

    # 6) Métadonnées JSON pour un document
    path(
        'documents/<int:doc_id>/metadata/',
        views.document_metadata,
        name='document_metadata'
    ),

    # 7) Suppression d'un document
    path(
        'document/<int:doc_id>/delete/',
        views.delete_document,
        name='document_delete'
    ),

    # 8) Édition manuelle des métadonnées
    path(
        'edit/<int:doc_id>/',
        views.edit_metadata,
        name='edit_metadata'
    ),

    # 9) Validation d'un document (extraction des pages)
    path(
        'document/<int:doc_id>/validate/',
        views.validate_document,
        name='validate_document'
    ),

    # 10) Dashboard métadonneur
    path(
        'dashboard/',
        views.dashboard_view,
        name='dashboard'
    ),

    # ——— URLs Annotateur —————————————————————————————————

    # 11) Dashboard annotation (liste des documents validés)
    path(
        'annotation/',
        views.annotation_dashboard,
        name='annotation_dashboard'
    ),

    # 12) Interface d'annotation d'un document spécifique
    path(
        'annotation/document/<int:doc_id>/',
        views.annotate_document,
        name='annotate_document'
    ),

    # 13) Annotation automatique avec Groq
    path(
        'annotation/groq/<int:page_id>/',
        views.ai_annotate_page_groq,
        name='ai_annotate_page_groq'
    ),

    # 14) Sauvegarde d'une annotation manuelle
    path(
        'annotation/manual/',
        views.save_manual_annotation,
        name='save_manual_annotation'
    ),

    # 15) Récupération des annotations d'une page
    path(
        'annotation/page/<int:page_id>/',
        views.get_page_annotations,
        name='get_page_annotations'
    ),

    # 16) Suppression d'une annotation
    path(
        'annotation/<int:annotation_id>/delete/',
        views.delete_annotation,
        name='delete_annotation'
    ),

    # 17) Validation des annotations d'une page (RLHF)
    path(
        'annotation/validate-page/<int:page_id>/',
        views.validate_page_annotations,
        name='validate_page_annotations'
    ),

    # 18) Dashboard d'apprentissage IA
    path(
        'learning/dashboard/',
        views.get_learning_dashboard,
        name='learning_dashboard'
    ),

    # ——— URLs Expert —————————————————————————————————————

    # 19) Soumission pour révision experte
    path(
        'submit-for-expert/<int:doc_id>/',
        views.submit_for_expert_review,
        name='submit_for_expert_review'
    ),

    # 20) Statut du document
    path(
        'document-status/<int:doc_id>/',
        views.get_document_status,
        name='document_status'
    ),

    # ——— URLs Gestion des annotations —————————————————————

    # 21) Création d'un type d'annotation personnalisé
    path(
        'create-annotation-type/',
        views.create_annotation_type,
        name='create_annotation_type'
    ),
    path('delete-annotation-type/', 
         views.delete_annotation_type, 
         name='delete_annotation_type'
    ),
    
    path('documents/<int:document_id>/view-original/', 
         views.view_original_document, 
         name='view_original_document'
    ),

]
