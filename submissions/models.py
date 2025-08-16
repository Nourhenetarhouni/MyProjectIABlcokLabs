from django.db import models
from django.contrib.auth.models import User
from django.urls import reverse


class Submission(models.Model):
    REGION_CHOICES = [
        ('EMA', 'Union Européenne (EMA)'),
        ('FDA', 'États-Unis (FDA)'),
        ('HC', 'Canada (Health Canada)'),
        ('PMDA', 'Japon (PMDA)'),
    ]

    VARIATION_TYPES = [
        ('IA', 'Variation Type IA'),
        ('IB', 'Variation Type IB'),
        ('II', 'Variation Type II'),
        ('MAA', 'Marketing Authorization Application'),
    ]

    STATUS_CHOICES = [
        ('draft', 'Draft'),
        ('in_progress', 'En cours'),
        ('submitted', 'Soumis'),
        ('approved', 'Approuvé'),
    ]

    name = models.CharField(max_length=100, verbose_name="Nom de la soumission")
    region = models.CharField(max_length=10, choices=REGION_CHOICES, verbose_name="Pays/Région")
    variation_type = models.CharField(max_length=10, choices=VARIATION_TYPES, verbose_name="Type de variation")
    change_description = models.TextField(verbose_name="Description du changement")
    status = models.CharField(max_length=20, choices=STATUS_CHOICES, default='draft', verbose_name="Statut")
    progress = models.IntegerField(default=0, verbose_name="Progression (%)")
    created_at = models.DateTimeField(auto_now_add=True)
    updated_at = models.DateTimeField(auto_now=True)
    created_by = models.ForeignKey(User, on_delete=models.CASCADE, related_name='submissions')

    class Meta:
        ordering = ['-created_at']
        verbose_name = "Soumission"
        verbose_name_plural = "Soumissions"

    def __str__(self):
        return f"{self.name} - {self.get_region_display()}"

    def get_absolute_url(self):
        return reverse('submissions:detail', kwargs={'pk': self.pk})


class SubmissionModule(models.Model):
    MODULE_TYPES = [
        ('M1', 'Module 1 - Administrative Information'),
        ('M2', 'Module 2 - Summaries'),
        ('M3', 'Module 3 - Quality'),
        ('M4', 'Module 4 - Nonclinical Study Reports'),
        ('M5', 'Module 5 - Clinical Study Reports'),
    ]

    submission = models.ForeignKey(Submission, on_delete=models.CASCADE, related_name='modules')
    module_type = models.CharField(max_length=2, choices=MODULE_TYPES)
    title = models.CharField(max_length=200)
    is_active = models.BooleanField(default=True)
    order = models.IntegerField(default=0)

    class Meta:
        ordering = ['order']
        unique_together = ['submission', 'module_type']

    def __str__(self):
        return f"{self.get_module_type_display()}"


class ModuleSection(models.Model):
    module = models.ForeignKey(SubmissionModule, on_delete=models.CASCADE, related_name='sections')
    section_number = models.CharField(max_length=10, verbose_name="Numéro de section")
    title = models.CharField(max_length=200, verbose_name="Titre")
    description = models.TextField(blank=True, verbose_name="Description")
    template_content = models.TextField(blank=True, verbose_name="Contenu du template")
    is_completed = models.BooleanField(default=False, verbose_name="Complété")
    order = models.IntegerField(default=0)

    class Meta:
        ordering = ['order']
        unique_together = ['module', 'section_number']

    def __str__(self):
        return f"{self.section_number} {self.title}"


class FormattedTemplate(models.Model):
    section = models.OneToOneField(ModuleSection, on_delete=models.CASCADE, related_name='formatted_template')
    template_name = models.CharField(max_length=200)
    version = models.CharField(max_length=50, default="Version 5")
    division = models.CharField(max_length=200, default="Information Management Division")
    date_created = models.DateField(auto_now_add=True)

    # Champs spécifiques au template formaté
    applicant_name = models.CharField(max_length=200, blank=True, verbose_name="Applicant/MAH Name")
    customer_account_number = models.CharField(max_length=100, blank=True, verbose_name="Customer Account Number")
    customer_reference = models.CharField(max_length=100, blank=True,
                                          verbose_name="Customer Reference / Purchase Order Number")
    inn_code = models.CharField(max_length=100, blank=True, verbose_name="INN / Active substance/ATC Code")
    product_name = models.CharField(max_length=200, blank=True,
                                    verbose_name="Product Name of centrally authorised medicinal product(s)")

    # Autres champs
    nationally_authorised = models.BooleanField(default=False, verbose_name="Nationally Authorised Product(s)")
    product_procedure_number = models.CharField(max_length=100, blank=True)
    national_marketing_auth_no = models.BooleanField(default=False)
    new_procedure = models.BooleanField(default=False, verbose_name="A submission of a new procedure")
    response_supplementary = models.BooleanField(default=False,
                                                 verbose_name="A response/supplementary information to an on-going procedure")

    unit_type = models.CharField(max_length=100, blank=True, verbose_name="Unit Type")
    mode_single = models.BooleanField(default=True, verbose_name="Single")
    mode_grouping = models.BooleanField(default=False, verbose_name="Grouping")
    procedure_type = models.CharField(max_length=200, default="MAA - Marketing Authorisation Application")
    description_submission = models.TextField(blank=True, verbose_name="Description of submission")

    related_products = models.TextField(blank=True,
                                        verbose_name="Centrally authorised medicinal products for which the same change(s) are being applied")
    rmp_included = models.BooleanField(default=False, verbose_name="RMP included in this submission")
    rmp_version = models.CharField(max_length=50, blank=True, verbose_name="RMP version")
    related_submission_numbers = models.CharField(max_length=200, blank=True, verbose_name="Related submission numbers")
    ectd_sequence = models.CharField(max_length=100, blank=True, verbose_name="eCTD sequence")

    contact_content = models.TextField(blank=True,
                                       verbose_name="Contact Persons' details (include email address) - Content")
    contact_technical = models.TextField(blank=True, verbose_name="Contact Persons' details - eCTD technical questions")

    def __str__(self):
        return f"Template: {self.template_name}"


class SubmissionSuggestion(models.Model):
    submission = models.ForeignKey(Submission, on_delete=models.CASCADE, related_name='suggestions')
    title = models.CharField(max_length=200)
    description = models.TextField()
    suggestion_type = models.CharField(max_length=50, choices=[
        ('structure', 'Structure CTD optimisée'),
        ('missing_section', 'Sections manquantes détectées'),
        ('recommendation', 'Recommandation'),
    ])
    is_applied = models.BooleanField(default=False)
    created_at = models.DateTimeField(auto_now_add=True)

    class Meta:
        ordering = ['-created_at']

    def __str__(self):
        return f"Suggestion: {self.title}"