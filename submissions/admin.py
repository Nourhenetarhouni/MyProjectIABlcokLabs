from django.contrib import admin
from .models import Submission, SubmissionModule, ModuleSection, FormattedTemplate, SubmissionSuggestion


class ModuleSectionInline(admin.TabularInline):
    model = ModuleSection
    extra = 0
    fields = ('section_number', 'title', 'is_completed', 'order')
    readonly_fields = ('section_number', 'title')


class SubmissionModuleInline(admin.TabularInline):
    model = SubmissionModule
    extra = 0
    fields = ('module_type', 'title', 'is_active', 'order')
    readonly_fields = ('module_type', 'title')


class SubmissionSuggestionInline(admin.TabularInline):
    model = SubmissionSuggestion
    extra = 0
    fields = ('title', 'suggestion_type', 'is_applied')
    readonly_fields = ('title', 'suggestion_type')


@admin.register(Submission)
class SubmissionAdmin(admin.ModelAdmin):
    list_display = ('name', 'region', 'variation_type', 'status', 'progress', 'created_by', 'created_at')
    list_filter = ('region', 'variation_type', 'status', 'created_at')
    search_fields = ('name', 'change_description', 'created_by__username')
    readonly_fields = ('created_at', 'updated_at')
    inlines = [SubmissionModuleInline, SubmissionSuggestionInline]

    fieldsets = (
        (None, {
            'fields': ('name', 'region', 'variation_type', 'change_description')
        }),
        ('Status', {
            'fields': ('status', 'progress')
        }),
        ('Metadata', {
            'fields': ('created_by', 'created_at', 'updated_at'),
            'classes': ('collapse',)
        }),
    )


@admin.register(SubmissionModule)
class SubmissionModuleAdmin(admin.ModelAdmin):
    list_display = ('submission', 'module_type', 'title', 'is_active', 'order')
    list_filter = ('module_type', 'is_active')
    search_fields = ('submission__name', 'title')
    inlines = [ModuleSectionInline]


@admin.register(ModuleSection)
class ModuleSectionAdmin(admin.ModelAdmin):
    list_display = ('module', 'section_number', 'title', 'is_completed', 'order')
    list_filter = ('is_completed', 'module__module_type')
    search_fields = ('title', 'section_number', 'module__submission__name')
    readonly_fields = ('section_number', 'title')


@admin.register(FormattedTemplate)
class FormattedTemplateAdmin(admin.ModelAdmin):
    list_display = ('section', 'template_name', 'version', 'date_created')
    list_filter = ('version', 'date_created')
    search_fields = ('template_name', 'section__title', 'applicant_name')
    readonly_fields = ('date_created',)

    fieldsets = (
        ('General Information', {
            'fields': ('section', 'template_name', 'version', 'division', 'date_created')
        }),
        ('Applicant Information', {
            'fields': ('applicant_name', 'customer_account_number', 'customer_reference')
        }),
        ('Product Information', {
            'fields': ('inn_code', 'product_name', 'nationally_authorised',
                       'product_procedure_number', 'national_marketing_auth_no')
        }),
        ('Procedure Information', {
            'fields': ('new_procedure', 'response_supplementary', 'unit_type',
                       'mode_single', 'mode_grouping', 'procedure_type', 'description_submission')
        }),
        ('Additional Information', {
            'fields': ('related_products', 'rmp_included', 'rmp_version',
                       'related_submission_numbers', 'ectd_sequence')
        }),
        ('Contact Information', {
            'fields': ('contact_content', 'contact_technical')
        }),
    )


@admin.register(SubmissionSuggestion)
class SubmissionSuggestionAdmin(admin.ModelAdmin):
    list_display = ('submission', 'title', 'suggestion_type', 'is_applied', 'created_at')
    list_filter = ('suggestion_type', 'is_applied', 'created_at')
    search_fields = ('title', 'description', 'submission__name')
    readonly_fields = ('created_at',)

    actions = ['mark_as_applied', 'mark_as_not_applied']

    def mark_as_applied(self, request, queryset):
        queryset.update(is_applied=True)
        self.message_user(request, f"{queryset.count()} suggestions marquées comme appliquées.")

    mark_as_applied.short_description = "Marquer comme appliquées"

    def mark_as_not_applied(self, request, queryset):
        queryset.update(is_applied=False)
        self.message_user(request, f"{queryset.count()} suggestions marquées comme non appliquées.")

    mark_as_not_applied.short_description = "Marquer comme non appliquées"