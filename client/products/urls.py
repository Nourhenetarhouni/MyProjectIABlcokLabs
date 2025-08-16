from django.urls import path
from . import views

app_name = 'client_products'

urlpatterns = [
    # Vues HTML
    path('', views.products_list_view, name='list'),
    path('<int:pk>/', views.product_detail_view, name='detail'),
    
    # API endpoints
    path('api/products/', views.ProductListAPIView.as_view(), name='api_list'),
    path('api/products/<int:pk>/', views.ProductDetailAPIView.as_view(), name='api_detail'),
    path('api/products/search/', views.search_products, name='api_search'),
    path('api/products/<int:pk>/overview/', views.product_overview, name='api_overview'),
    path('api/products/<int:pk>/sites/', views.product_sites, name='api_sites'),
    path('api/products/<int:pk>/variations/', views.product_variations, name='api_variations'),
    path('api/products/<int:pk>/source-document/', views.product_source_document_view, name='source_document'),
    path('api/products/<int:pk>/variations/add/', views.add_product_variation, name='api_add_variation'),


]