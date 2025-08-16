import os
from django import template

register = template.Library()

@register.filter
def clean_filename(file_field):
    """Extract clean filename from file path, removing timestamp prefix"""
    if not file_field:
        return ""
    
    filename = os.path.basename(file_field.name)
    
    # Remove timestamp prefix (format: 20250722_024000/filename.pdf)
    if '/' in filename:
        filename = filename.split('/')[-1]
    
    # Remove file extension for display
    name_without_ext = os.path.splitext(filename)[0]
    
    # Clean up the name (replace underscores with spaces, capitalize)
    clean_name = name_without_ext.replace('_', ' ').replace('-', ' ')
    
    return clean_name

@register.filter
def document_title(document):
    """Get document title with proper fallback to filename"""
    if document.title and document.title.strip():
        return document.title.strip()
    
    if document.file:
        clean_name = clean_filename(document.file)
        if clean_name:
            return clean_name
    
    return "Document sans titre"