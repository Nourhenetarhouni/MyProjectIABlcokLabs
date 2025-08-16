from django.contrib import admin
from .models import ReportSubmission, ReportKPI, ReportHeatmap

@admin.register(ReportSubmission)
class ReportSubmissionAdmin(admin.ModelAdmin):
    list_display = ['product', 'type', 'status', 'submission_date', 'responsible', 'progress']
    list_filter = ['status', 'type', 'team']
    search_fields = ['product__name', 'responsible']
    date_hierarchy = 'submission_date'
    
    def get_queryset(self, request):
        return super().get_queryset(request).select_related('product')

@admin.register(ReportKPI)
class ReportKPIAdmin(admin.ModelAdmin):
    list_display = ['date', 'period', 'total_submissions', 'success_rate', 'delayed_count']
    list_filter = ['period', 'date']
    readonly_fields = ['date']
    
@admin.register(ReportHeatmap)
class ReportHeatmapAdmin(admin.ModelAdmin):
    list_display = ['product', 'date', 'authorization_delay', 'variation_delay', 'renewal_delay']
    list_filter = ['date', 'authorization_status', 'variation_status', 'renewal_status']
    search_fields = ['product__name']
    
    def get_queryset(self, request):
        return super().get_queryset(request).select_related('product')