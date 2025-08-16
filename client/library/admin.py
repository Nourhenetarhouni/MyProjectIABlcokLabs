from django.contrib import admin
from .models import DocumentCategory, RegulatoryAuthority, Document, DocumentVersion, DocumentTranslation

@admin.register(DocumentCategory)
class DocumentCategoryAdmin(admin.ModelAdmin):
    list_display = ['name', 'code', 'color']
    list_editable = ['color']
    search_fields = ['name', 'code']

@admin.register(RegulatoryAuthority)
class RegulatoryAuthorityAdmin(admin.ModelAdmin):
    list_display = ['name', 'code', 'country', 'website']
    list_filter = ['country']
    search_fields = ['name', 'code', 'country']

@admin.register(Document)
class DocumentAdmin(admin.ModelAdmin):
    list_display = ['title', 'document_type', 'authority', 'language', 'validation_status', 'publication_date', 'view_count']
    list_filter = ['document_type', 'authority', 'language', 'validation_status', 'publication_date']
    search_fields = ['title', 'description', 'reference_number', 'tags']
    readonly_fields = ['view_count', 'download_count', 'created_at', 'updated_at', 'file_size']
    filter_horizontal = []
    
    fieldsets = (
        ('Informations principales', {
            'fields': ('title', 'description', 'document_type', 'category')
        }),
        ('Source et autorité', {
            'fields': ('authority', 'source_url', 'reference_number')
        }),
        ('Fichier et langue', {
            'fields': ('file', 'file_size', 'language')
        }),
        ('Dates', {
            'fields': ('publication_date', 'effective_date', 'expiry_date')
        }),
        ('Validation', {
            'fields': ('validation_status', 'validated_by', 'validation_date', 'validation_notes')
        }),
        ('Classification', {
            'fields': ('tags', 'ctd_section', 'therapeutic_area')
        }),
        ('Métadonnées système', {
            'fields': ('created_by', 'created_at', 'updated_at'),
            'classes': ('collapse',)
        }),
        ('Statistiques', {
            'fields': ('view_count', 'download_count'),
            'classes': ('collapse',)
        }),
    )
    
    def save_model(self, request, obj, form, change):
        if not change:  # Si c'est un nouveau document
            obj.created_by = request.user.username
        
        # Calculer la taille du fichier si elle n'est pas définie
        if obj.file and not obj.file_size:
            try:
                obj.file_size = obj.file.size
            except:
                pass
                
        super().save_model(request, obj, form, change)

@admin.register(DocumentVersion)
class DocumentVersionAdmin(admin.ModelAdmin):
    list_display = ['document', 'version', 'created_at', 'created_by']
    list_filter = ['created_at']
    search_fields = ['document__title', 'version', 'release_notes']

@admin.register(DocumentTranslation)
class DocumentTranslationAdmin(admin.ModelAdmin):
    list_display = ['original_document', 'language', 'translation_method', 'validated', 'created_at']
    list_filter = ['language', 'translation_method', 'validated']
    search_fields = ['original_document__title', 'title']
