# expert/admin.py

from django.contrib import admin
from django.utils.html import format_html
from .models import ExpertLog


@admin.register(ExpertLog)
class ExpertLogAdmin(admin.ModelAdmin):
    list_display = ['expert', 'action', 'annotation_text', 'annotation_entity_type', 'original_annotator', 'timestamp']
    list_filter = ['action', 'annotation_entity_type', 'timestamp', 'expert']
    search_fields = ['document_title', 'annotation_text', 'expert__username', 'original_annotator']
    readonly_fields = ['timestamp']
    ordering = ['-timestamp']

    def changelist_view(self, request, extra_context=None):
        extra_context = extra_context or {}
        extra_context['title'] = 'Logs des Actions Expert'
        return super().changelist_view(request, extra_context=extra_context)