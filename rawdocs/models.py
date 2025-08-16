from os.path import join
from datetime import datetime
from django.db import models
from django.conf import settings
from django.contrib.auth.models import User


def pdf_upload_to(instance, filename):
    """
    Place chaque PDF téléchargé dans un sous-dossier horodaté.
    Ex. "20250626_143502/mon_document.pdf"
    """
    ts = datetime.now().strftime('%Y%m%d_%H%M%S')
    return join(ts, filename)


class RawDocument(models.Model):
    # Source & stockage
    url = models.URLField(help_text="URL d'origine du PDF", blank=True)
    file = models.FileField(upload_to=pdf_upload_to, help_text="Fichier PDF téléchargé")
    created_at = models.DateTimeField(auto_now_add=True)

    # Ownership
    owner = models.ForeignKey(
        settings.AUTH_USER_MODEL,
        on_delete=models.CASCADE,
        related_name='raw_documents',
        null=True, blank=True,
        help_text="Utilisateur qui a téléchargé ce document"
    )

    # Statut de validation
    is_validated = models.BooleanField(default=False, help_text="Document validé par un métadonneur")
    validated_at = models.DateTimeField(null=True, blank=True)
    # Expert review status
    is_ready_for_expert = models.BooleanField(default=False, help_text="Document prêt pour révision expert")
    expert_ready_at = models.DateTimeField(null=True, blank=True,
                                           help_text="Date à laquelle le document est devenu prêt pour l'expert")

    # Extraction de pages
    total_pages = models.IntegerField(default=0, help_text="Nombre total de pages")
    pages_extracted = models.BooleanField(default=False, help_text="Pages extraites individuellement")

    # Métadonnées extraites
    title = models.TextField(blank=True, help_text="Titre du document")
    doc_type = models.CharField("Type", max_length=100, blank=True, help_text="Type du document (guide, rapport…)")
    publication_date = models.CharField(max_length=100, blank=True, help_text="Date de publication")
    version = models.CharField(max_length=50, blank=True, help_text="Version extraite")
    source = models.CharField(max_length=255, blank=True, help_text="Organisation émettrice (EMA, FDA…)")
    context = models.TextField(blank=True, help_text="Contexte extrait (2 phrases max)")
    country = models.CharField(max_length=100, blank=True, help_text="Pays détecté (GPE ou TLD)")
    language = models.CharField(max_length=10, blank=True, help_text="Langue détectée (fr, en…)")
    url_source = models.URLField(blank=True, help_text="URL d'origine pour référence")

    def __str__(self):
        owner_name = self.owner.username if self.owner else "–"
        status = "✅ Validé" if self.is_validated else "⏳ En attente"
        return f"PDF #{self.pk} ({status}) – par {owner_name}"


class MetadataLog(models.Model):
    document = models.ForeignKey('RawDocument', on_delete=models.CASCADE, related_name='logs')
    field_name = models.CharField(max_length=100)
    old_value = models.TextField(null=True, blank=True)
    new_value = models.TextField(null=True, blank=True)
    modified_at = models.DateTimeField(auto_now_add=True)
    modified_by = models.ForeignKey(User, on_delete=models.SET_NULL, null=True)

    def __str__(self):
        return f"{self.field_name}: {self.old_value} → {self.new_value}"


class DocumentPage(models.Model):
    """Pages individuelles extraites du PDF."""
    document = models.ForeignKey(RawDocument, on_delete=models.CASCADE, related_name='pages')
    page_number = models.IntegerField(help_text="Numéro de page (1-indexé)")
    raw_text = models.TextField(help_text="Texte brut extrait de la page")
    cleaned_text = models.TextField(help_text="Texte nettoyé pour annotation")

    # Statut d'annotation
    is_annotated = models.BooleanField(default=False)
    annotated_at = models.DateTimeField(null=True, blank=True)
    annotated_by = models.ForeignKey(
        settings.AUTH_USER_MODEL,
        on_delete=models.SET_NULL,
        null=True, blank=True,
        related_name='annotated_pages'
    )

    # Validation humaine
    is_validated_by_human = models.BooleanField(default=False)
    human_validated_at = models.DateTimeField(null=True, blank=True)
    validated_by = models.ForeignKey(
        settings.AUTH_USER_MODEL,
        on_delete=models.SET_NULL,
        null=True, blank=True,
        related_name='validated_pages'
    )

    created_at = models.DateTimeField(auto_now_add=True)

    class Meta:
        unique_together = ['document', 'page_number']
        ordering = ['page_number']

    def __str__(self):
        return f"Page {self.page_number} – Doc #{self.document.pk}"


class AnnotationType(models.Model):
    """Types d'annotations possibles."""
    name = models.CharField(max_length=100, unique=True)
    display_name = models.CharField(max_length=100, help_text="Libellé affiché")
    color = models.CharField(max_length=7, default="#3b82f6", help_text="Couleur hexadécimale")
    description = models.TextField(blank=True)

    # Predefined types
    PROCEDURE_TYPE = "procedure_type"
    COUNTRY = "country"
    AUTHORITY = "authority"
    LEGAL_REFERENCE = "legal_reference"
    REQUIRED_DOCUMENT = "required_document"
    REQUIRED_CONDITION = "required_condition"
    DELAY = "delay"
    VARIATION_CODE = "variation_code"
    FILE_TYPE = "file_type"

    created_at = models.DateTimeField(auto_now_add=True)

    def __str__(self):
        return self.display_name


class Annotation(models.Model):
    """Annotation sur une page de document."""
    page = models.ForeignKey(DocumentPage, on_delete=models.CASCADE, related_name='annotations')
    annotation_type = models.ForeignKey(AnnotationType, on_delete=models.CASCADE)

    # Text selection
    start_pos = models.IntegerField(help_text="Position de début dans le texte")
    end_pos = models.IntegerField(help_text="Position de fin dans le texte")
    selected_text = models.CharField(max_length=500, help_text="Texte sélectionné")

    # AI confidence and context
    confidence_score = models.FloatField(default=0.0, help_text="Score IA (0.0–1.0)")
    ai_reasoning = models.TextField(blank=True, help_text="Raisonnement IA pour cette annotation")

    # Expert validation status
    VALIDATION_CHOICES = [
        ('pending', 'En attente'),
        ('validated', 'Validé'),
        ('rejected', 'Rejeté'),
        ('expert_created', 'Créé par expert'),
    ]

    validation_status = models.CharField(
        max_length=20,
        choices=VALIDATION_CHOICES,
        default='pending',
        help_text="Statut de validation par l'expert"
    )

    # Source tracking
    SOURCE_CHOICES = [
        ('ai', 'Intelligence Artificielle'),
        ('manual', 'Manuel'),
        ('expert', 'Expert'),
    ]
    source = models.CharField(max_length=10, choices=SOURCE_CHOICES, default='ai')

    # Manual validation
    is_validated = models.BooleanField(default=False)
    validated_by = models.ForeignKey(
        settings.AUTH_USER_MODEL,
        on_delete=models.SET_NULL,
        null=True, blank=True,
        related_name='validated_annotations'
    )
    validated_at = models.DateTimeField(null=True, blank=True)

    # Metadata
    created_at = models.DateTimeField(auto_now_add=True)
    created_by = models.ForeignKey(
        settings.AUTH_USER_MODEL,
        on_delete=models.SET_NULL,
        null=True, blank=True,
        related_name='created_annotations'
    )

    class Meta:
        ordering = ['start_pos']

    def __str__(self):
        sel = (self.selected_text[:47] + '...') if len(self.selected_text) > 50 else self.selected_text
        return f"{self.annotation_type.display_name}: '{sel}'"


class UserProfile(models.Model):
    ROLE_CHOICES = [
        ('metadonneur', 'Métadonneur'),
        ('annotateur', 'Annotateur'),
        ('expert', 'Expert'),
        ('client', 'Client'),
    ]

    user = models.OneToOneField(User, on_delete=models.CASCADE)
    role = models.CharField(max_length=20, choices=ROLE_CHOICES, default='client')

    def __str__(self):
        return f"{self.user.username} - {self.role}"


class AnnotationSession(models.Model):
    """Session d'annotation pour analytics."""
    document = models.ForeignKey(RawDocument, on_delete=models.CASCADE, related_name='annotation_sessions')
    annotator = models.ForeignKey(settings.AUTH_USER_MODEL, on_delete=models.CASCADE)

    # Session stats
    total_annotations = models.IntegerField(default=0)
    pages_annotated = models.IntegerField(default=0)
    ai_annotations = models.IntegerField(default=0)
    manual_annotations = models.IntegerField(default=0)

    # Timing
    started_at = models.DateTimeField(auto_now_add=True)
    finished_at = models.DateTimeField(null=True, blank=True)
    duration_minutes = models.IntegerField(default=0)

    def __str__(self):
        return f"Session {self.annotator.username} – Doc #{self.document.pk}"


class AnnotationFeedback(models.Model):
    """Track human feedback for AI annotations"""
    page = models.ForeignKey(DocumentPage, on_delete=models.CASCADE, related_name='feedbacks')
    annotator = models.ForeignKey(settings.AUTH_USER_MODEL, on_delete=models.CASCADE)

    # AI's original predictions
    ai_annotations_before = models.JSONField(help_text="AI annotations before human correction")

    # Human corrections
    human_annotations_after = models.JSONField(help_text="Final annotations after human validation")

    # Feedback analysis
    corrections_made = models.JSONField(help_text="What was corrected: additions, deletions, modifications")
    feedback_score = models.FloatField(default=0.0, help_text="Overall feedback score (0-1)")

    # Timestamps
    validated_at = models.DateTimeField(auto_now_add=True)

    class Meta:
        unique_together = ['page', 'annotator']


class AILearningMetrics(models.Model):
    """Track AI performance over time"""
    model_version = models.CharField(max_length=50, default="groq_llama3.3_70b")

    # Performance metrics
    precision_score = models.FloatField(default=0.0)
    recall_score = models.FloatField(default=0.0)
    f1_score = models.FloatField(default=0.0)

    # Learning data
    total_feedbacks = models.IntegerField(default=0)
    improvement_rate = models.FloatField(default=0.0)

    # Entity-specific performance
    entity_performance = models.JSONField(default=dict, help_text="Performance per entity type")

    created_at = models.DateTimeField(auto_now_add=True)


class PromptOptimization(models.Model):
    """Store optimized prompts based on learning"""
    entity_type = models.CharField(max_length=100)
    optimized_prompt = models.TextField()
    performance_score = models.FloatField()
    feedback_count = models.IntegerField(default=0)

    created_at = models.DateTimeField(auto_now_add=True)
    is_active = models.BooleanField(default=True)