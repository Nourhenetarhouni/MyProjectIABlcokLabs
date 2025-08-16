# expert/models.py

from django.db import models
from django.contrib.auth.models import User
from django.utils import timezone
import uuid


class ExpertLog(models.Model):
    """Logs des actions de l'expert"""

    ACTION_CHOICES = [
        ('annotation_validated', 'Annotation validée'),
        ('annotation_rejected', 'Annotation rejetée'),
        ('annotation_modified', 'Annotation modifiée'),
        ('annotation_deleted', 'Annotation supprimée'),
        ('annotation_created', 'Annotation créée'),
        ('validation_undone', 'Validation annulée'),
        ('document_reviewed', 'Document révisé'),
        ('sentence_reviewed', 'Phrase révisée'),
        ('annotation_type_created', 'Type d\'annotation créé'),
        ('annotation_type_deleted', 'Type d\'annotation supprimé'),
        ('document_validated_product_created', 'Document validé et produit créé'),
    ]

    # Info utilisateur et timing
    expert = models.ForeignKey(User, on_delete=models.CASCADE, related_name='expert_logs')
    timestamp = models.DateTimeField(auto_now_add=True)
    session_id = models.CharField(max_length=100, blank=True)

    # Info document/phrase
    document_id = models.IntegerField()
    document_title = models.CharField(max_length=500)
    page_id = models.IntegerField(null=True, blank=True)
    page_number = models.IntegerField(null=True, blank=True)
    page_text = models.TextField(blank=True)

    # Détails de l'action
    action = models.CharField(max_length=60, choices=ACTION_CHOICES)
    annotation_id = models.IntegerField(null=True, blank=True, help_text="ID de l'annotation concernée")

    # Détails de l'annotation
    annotation_text = models.TextField(blank=True, help_text="Texte de l'annotation")
    annotation_entity_type = models.CharField(max_length=100, blank=True)
    annotation_start_position = models.IntegerField(null=True, blank=True)
    annotation_end_position = models.IntegerField(null=True, blank=True)

    # Pour les modifications : avant/après
    old_text = models.TextField(blank=True, help_text="Ancien texte (pour modifications)")
    new_text = models.TextField(blank=True, help_text="Nouveau texte (pour modifications)")
    old_entity_type = models.CharField(max_length=100, blank=True)
    new_entity_type = models.CharField(max_length=100, blank=True)

    # Métadonnées
    original_annotator = models.CharField(max_length=150, blank=True, help_text="Qui a créé l'annotation originale")
    validation_status_before = models.CharField(max_length=50, blank=True)
    validation_status_after = models.CharField(max_length=50, blank=True)
    reason = models.TextField(blank=True, help_text="Raison de l'action")
    time_spent_seconds = models.IntegerField(null=True, blank=True)

    class Meta:
        verbose_name = "Log Expert"
        verbose_name_plural = "Logs Expert"
        ordering = ['-timestamp']

    def __str__(self):
        return f"{self.expert.username} - {self.get_action_display()} - {self.timestamp.strftime('%d/%m/%Y %H:%M')}"

    @property
    def detailed_description(self):
        """Description détaillée de l'action"""
        descriptions = {
            'annotation_validated': f"A validé l'annotation '{self.annotation_text}' ({self.annotation_entity_type}) créée par {self.original_annotator}",
            'annotation_rejected': f"A rejeté l'annotation '{self.annotation_text}' ({self.annotation_entity_type}) créée par {self.original_annotator}",
            'annotation_modified': f"A modifié l'annotation de '{self.old_text}' ({self.old_entity_type}) vers '{self.new_text}' ({self.new_entity_type})",
            'annotation_deleted': f"A supprimé l'annotation '{self.annotation_text}' ({self.annotation_entity_type})",
            'annotation_created': f"A créé une nouvelle annotation '{self.annotation_text}' ({self.annotation_entity_type})",
            'validation_undone': f"A annulé la validation de l'annotation '{self.annotation_text}' ({self.annotation_entity_type})",
        }

        base = descriptions.get(self.action, f"{self.get_action_display()}: {self.annotation_text}")
        context = f" dans la page {self.page_number} du document '{self.document_title}'"

        return base + context

    @property
    def change_summary(self):
        """Résumé des changements pour les modifications"""
        if self.action == 'annotation_modified':
            changes = []
            if self.old_text != self.new_text:
                changes.append(f"Texte: '{self.old_text}' → '{self.new_text}'")
            if self.old_entity_type != self.new_entity_type:
                changes.append(f"Type: {self.old_entity_type} → {self.new_entity_type}")
            return " | ".join(changes)
        return ""