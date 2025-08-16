from django import template

register = template.Library()

@register.filter
def document_title(document):
    """
    Retourne le titre du document ou un titre par défaut
    """
    if document.title and document.title.strip():
        return document.title
    return f"Document #{document.pk}"