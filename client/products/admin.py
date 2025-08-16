from django.contrib import admin
from .models import Product, ProductSpecification, ManufacturingSite, ProductVariation

@admin.register(Product)
class ProductAdmin(admin.ModelAdmin):
    list_display = ['name', 'active_ingredient', 'status', 'created_at']
    list_filter = ['status', 'therapeutic_area']
    search_fields = ['name', 'active_ingredient']
    readonly_fields = ['created_at', 'updated_at']

@admin.register(ProductSpecification)
class ProductSpecificationAdmin(admin.ModelAdmin):
    list_display = ['product', 'country_code', 'amm_number', 'approval_date', 'is_active']
    list_filter = ['country_code', 'is_active']
    search_fields = ['product__name', 'amm_number']

@admin.register(ManufacturingSite)
class ManufacturingSiteAdmin(admin.ModelAdmin):
    list_display = ['site_name', 'country', 'city', 'gmp_certified']
    list_filter = ['country', 'gmp_certified']
    search_fields = ['site_name', 'city']

@admin.register(ProductVariation)
class ProductVariationAdmin(admin.ModelAdmin):
    list_display = ['title', 'product', 'variation_type', 'status', 'submission_date']
    list_filter = ['variation_type', 'status']
    search_fields = ['title', 'product__name']