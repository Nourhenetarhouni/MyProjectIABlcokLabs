# expert/urls.py

from django.urls import path
from . import views

app_name = 'expert'

urlpatterns = [
    path('', views.ExpertDashboardView.as_view(), name='dashboard'),
    path('documents/', views.DocumentReviewListView.as_view(), name='document_list'),
    path('review/<int:document_id>/', views.DocumentReviewView.as_view(), name='review_document'),
    path('validate-document/<int:document_id>/', views.validate_document, name='validate_document'),
    path('api/validate/<int:annotation_id>/', views.validate_annotation_ajax, name='validate_annotation'),
    path('api/create-annotation/', views.create_annotation_ajax, name='create_annotation'),
    path('api/modify/<int:annotation_id>/', views.modify_annotation_ajax, name='modify_annotation'),
    path('api/delete/<int:annotation_id>/', views.delete_annotation_ajax, name='delete_annotation'),
    path('api/undo/<int:annotation_id>/', views.undo_validation_ajax, name='undo_validation'),
    path('api/create-annotation-type/', views.create_annotation_type_ajax, name='create_annotation_type'),
    path('api/delete-annotation-type/', views.delete_annotation_type_ajax, name='delete_annotation_type'),
    path('documents/<int:document_id>/view-original/', views.view_original_document, name='view_original_document'),


]