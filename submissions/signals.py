from django.db.models.signals import post_save, pre_delete
from django.dispatch import receiver
from django.contrib.auth.models import User
from .models import Submission, SubmissionModule, ModuleSection


@receiver(post_save, sender=Submission)
def submission_created_handler(sender, instance, created, **kwargs):
    """
    Signal déclenché après la création d'une soumission
    """
    if created:
        # Logique automatique après création d'une soumission
        # Par exemple, envoyer une notification, créer des logs, etc.
        print(f"Nouvelle soumission créée: {instance.name}")


@receiver(post_save, sender=ModuleSection)
def section_completed_handler(sender, instance, **kwargs):
    """
    Signal déclenché quand une section est marquée comme complétée
    """
    if instance.is_completed:
        # Mettre à jour le pourcentage de progression de la soumission
        submission = instance.module.submission
        total_sections = ModuleSection.objects.filter(module__submission=submission).count()
        completed_sections = ModuleSection.objects.filter(
            module__submission=submission,
            is_completed=True
        ).count()

        if total_sections > 0:
            progress = int((completed_sections / total_sections) * 100)
            submission.progress = progress

            # Mettre à jour le statut selon la progression
            if progress == 100:
                submission.status = 'submitted'
            elif progress > 0:
                submission.status = 'in_progress'

            submission.save()


@receiver(pre_delete, sender=Submission)
def submission_cleanup_handler(sender, instance, **kwargs):
    """
    Nettoyage avant la suppression d'une soumission
    """
    # Nettoyer les fichiers associés, logs, etc.
    print(f"Suppression de la soumission: {instance.name}")