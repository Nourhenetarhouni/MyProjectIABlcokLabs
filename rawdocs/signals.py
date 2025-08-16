from django.db.models.signals import post_save, post_delete
from django.dispatch import receiver
from django.core.cache import cache
from .models import RawDocument

@receiver(post_save, sender=RawDocument)
def clear_document_stats_cache_on_save(sender, instance, **kwargs):
    """
    Vider le cache des statistiques quand un document est créé/modifié
    """
    cache.delete('document_type_stats')
    cache.delete('country_stats') 
    cache.delete('source_categories')
    cache.delete('total_documents')

@receiver(post_delete, sender=RawDocument)
def clear_document_stats_cache_on_delete(sender, instance, **kwargs):
    """
    Vider le cache des statistiques quand un document est supprimé
    """
    cache.delete('document_type_stats')
    cache.delete('country_stats')
    cache.delete('source_categories') 
    cache.delete('total_documents')