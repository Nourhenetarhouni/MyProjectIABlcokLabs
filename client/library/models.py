from django.db import models
from django.utils import timezone
from django.urls import reverse
import uuid
import os

class DocumentCategory(models.Model):
    """Catégories de documents réglementaires"""
    name = models.CharField(max_length=100, verbose_name="Nom de la catégorie")
    code = models.CharField(max_length=20, unique=True, verbose_name="Code")
    description = models.TextField(blank=True, verbose_name="Description")
    color = models.CharField(max_length=7, default="#3498db", verbose_name="Couleur")
    
    class Meta:
        verbose_name = "Catégorie de document"
        verbose_name_plural = "Catégories de documents"
        ordering = ['name']
    
    def __str__(self):
        return self.name

class RegulatoryAuthority(models.Model):
    """Autorités réglementaires"""
    name = models.CharField(max_length=200, verbose_name="Nom de l'autorité")
    code = models.CharField(max_length=10, unique=True, verbose_name="Code")
    country = models.CharField(max_length=100, verbose_name="Pays")
    website = models.URLField(blank=True, verbose_name="Site web")
    
    class Meta:
        verbose_name = "Autorité réglementaire"
        verbose_name_plural = "Autorités réglementaires"
        ordering = ['name']
    
    def __str__(self):
        return f"{self.name} ({self.code})"

def document_upload_path(instance, filename):
    """Génère le chemin d'upload pour les documents"""
    ext = filename.split('.')[-1]
    filename = f"{uuid.uuid4()}.{ext}"
    # Utiliser l'année actuelle si created_at n'existe pas encore
    year = instance.created_at.year if instance.created_at else timezone.now().year
    return os.path.join('documents', str(year), filename)

class Document(models.Model):
    """Documents réglementaires stockés dans la library"""
    
    DOCUMENT_TYPES = [
        ('guideline', 'Guideline'),
        ('regulation', 'Régulation'),
        ('gmp', 'GMP'),
        ('ich', 'ICH'),
        ('qa', 'Q&A'),
        ('template', 'Template'),
        ('other', 'Autre'),
    ]
    
    LANGUAGES = [
        ('en', 'English'),
        ('fr', 'Français'),
        ('de', 'Deutsch'),
        ('es', 'Español'),
        ('it', 'Italiano'),
        ('multi', 'Multilingue'),
    ]
    
    VALIDATION_STATUS = [
        ('pending', 'En attente de validation'),
        ('validated', 'Validé'),
        ('rejected', 'Rejeté'),
        ('expired', 'Expiré'),
    ]
    
    # Informations principales
    title = models.CharField(max_length=500, verbose_name="Titre")
    description = models.TextField(blank=True, verbose_name="Description")
    document_type = models.CharField(max_length=20, choices=DOCUMENT_TYPES, verbose_name="Type de document")
    category = models.ForeignKey(DocumentCategory, on_delete=models.SET_NULL, null=True, verbose_name="Catégorie")
    
    # Autorité et source
    authority = models.ForeignKey(RegulatoryAuthority, on_delete=models.CASCADE, verbose_name="Autorité réglementaire")
    source_url = models.URLField(blank=True, verbose_name="URL source")
    reference_number = models.CharField(max_length=100, blank=True, verbose_name="Numéro de référence")
    
    # Fichier et métadonnées
    file = models.FileField(upload_to=document_upload_path, verbose_name="Fichier")
    file_size = models.PositiveIntegerField(null=True, blank=True, verbose_name="Taille du fichier (bytes)")
    language = models.CharField(max_length=10, choices=LANGUAGES, default='en', verbose_name="Langue")
    
    # Dates importantes
    publication_date = models.DateField(verbose_name="Date de publication")
    effective_date = models.DateField(null=True, blank=True, verbose_name="Date d'entrée en vigueur")
    expiry_date = models.DateField(null=True, blank=True, verbose_name="Date d'expiration")
    
    # Validation et statut
    validation_status = models.CharField(max_length=20, choices=VALIDATION_STATUS, default='pending', verbose_name="Statut de validation")
    validated_by = models.CharField(max_length=100, blank=True, verbose_name="Validé par")
    validation_date = models.DateTimeField(null=True, blank=True, verbose_name="Date de validation")
    validation_notes = models.TextField(blank=True, verbose_name="Notes de validation")
    
    # Tags et classification
    tags = models.CharField(max_length=500, blank=True, verbose_name="Tags (séparés par des virgules)")
    ctd_section = models.CharField(max_length=50, blank=True, verbose_name="Section CTD")
    therapeutic_area = models.CharField(max_length=200, blank=True, verbose_name="Zone thérapeutique")
    
    # Métadonnées système
    created_at = models.DateTimeField(auto_now_add=True)
    updated_at = models.DateTimeField(auto_now=True)
    created_by = models.CharField(max_length=100, blank=True, verbose_name="Créé par")
    
    # Statistiques d'usage
    download_count = models.PositiveIntegerField(default=0, verbose_name="Nombre de téléchargements")
    view_count = models.PositiveIntegerField(default=0, verbose_name="Nombre de vues")
    
    class Meta:
        verbose_name = "Document"
        verbose_name_plural = "Documents"
        ordering = ['-created_at']
        indexes = [
            models.Index(fields=['document_type']),
            models.Index(fields=['validation_status']),
            models.Index(fields=['authority']),
            models.Index(fields=['publication_date']),
        ]
    
    def __str__(self):
        return self.title
    
    def get_absolute_url(self):
        return reverse('library:document_detail', kwargs={'pk': self.pk})
    
    @property
    def file_extension(self):
        if self.file:
            return os.path.splitext(self.file.name)[1].lower()
        return ''
    
    @property
    def formatted_file_size(self):
        if not self.file_size:
            return "N/A"
        
        # Convert bytes to human readable format
        for unit in ['B', 'KB', 'MB', 'GB']:
            if self.file_size < 1024.0:
                return f"{self.file_size:.1f} {unit}"
            self.file_size /= 1024.0
        return f"{self.file_size:.1f} TB"
    
    @property
    def is_expired(self):
        if self.expiry_date:
            return self.expiry_date < timezone.now().date()
        return False
    
    @property
    def tags_list(self):
        if self.tags:
            return [tag.strip() for tag in self.tags.split(',') if tag.strip()]
        return []

class DocumentVersion(models.Model):
    """Versions des documents pour traçabilité"""
    document = models.ForeignKey(Document, on_delete=models.CASCADE, related_name='versions')
    version = models.CharField(max_length=20, verbose_name="Version")
    file = models.FileField(upload_to=document_upload_path, verbose_name="Fichier")
    release_notes = models.TextField(blank=True, verbose_name="Notes de version")
    created_at = models.DateTimeField(auto_now_add=True)
    created_by = models.CharField(max_length=100, blank=True, verbose_name="Créé par")
    
    class Meta:
        verbose_name = "Version de document"
        verbose_name_plural = "Versions de documents"
        ordering = ['-created_at']
        unique_together = ['document', 'version']
    
    def __str__(self):
        return f"{self.document.title} v{self.version}"

class DocumentTranslation(models.Model):
    """Traductions des documents"""
    original_document = models.ForeignKey(Document, on_delete=models.CASCADE, related_name='translations')
    language = models.CharField(max_length=10, choices=Document.LANGUAGES, verbose_name="Langue de traduction")
    title = models.CharField(max_length=500, verbose_name="Titre traduit")
    description = models.TextField(blank=True, verbose_name="Description traduite")
    file = models.FileField(upload_to=document_upload_path, verbose_name="Fichier traduit")
    translation_method = models.CharField(max_length=20, choices=[('manual', 'Manuel'), ('ai', 'IA'), ('hybrid', 'Hybride')], verbose_name="Méthode de traduction")
    validated = models.BooleanField(default=False, verbose_name="Traduction validée")
    validated_by = models.CharField(max_length=100, blank=True, verbose_name="Validé par")
    created_at = models.DateTimeField(auto_now_add=True)
    
    class Meta:
        verbose_name = "Traduction de document"
        verbose_name_plural = "Traductions de documents"
        unique_together = ['original_document', 'language']
    
    def __str__(self):
        return f"{self.original_document.title} ({self.get_language_display()})"
