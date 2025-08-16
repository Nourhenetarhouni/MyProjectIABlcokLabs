#!/usr/bin/env python
"""
Script pour mettre à jour les métadonnées des documents existants avec l'extraction LLM
"""
import os
import sys
import django

# Configuration Django
os.environ.setdefault('DJANGO_SETTINGS_MODULE', 'MyProject.settings')
django.setup()

from rawdocs.models import RawDocument
from rawdocs.utils import extract_metadonnees

def update_document_metadata():
    """Met à jour les métadonnées des documents qui n'en ont pas"""
    
    # Trouver les documents sans métadonnées (titre ou source vides)
    documents_to_update = RawDocument.objects.filter(
        models.Q(title='') | models.Q(source='') | models.Q(title__isnull=True) | models.Q(source__isnull=True)
    )
    
    print(f"🔍 Trouvé {documents_to_update.count()} documents à mettre à jour")
    
    for doc in documents_to_update:
        if doc.file and os.path.exists(doc.file.path):
            print(f"\n📄 Traitement du document ID {doc.id}: {doc.file.name}")
            
            try:
                # Extraire les métadonnées avec le LLM
                metadata = extract_metadonnees(doc.file.path, doc.url or "")
                
                if metadata:
                    # Sauvegarder les métadonnées dans les champs du modèle
                    doc.title = metadata.get('title', '')
                    doc.doc_type = metadata.get('type', '')
                    doc.publication_date = metadata.get('publication_date', '')
                    doc.version = metadata.get('version', '')
                    doc.source = metadata.get('source', '')
                    doc.context = metadata.get('context', '')
                    doc.country = metadata.get('country', '')
                    doc.language = metadata.get('language', '')
                    doc.url_source = metadata.get('url_source', doc.url or '')
                    doc.save()
                    
                    print(f"✅ Métadonnées mises à jour:")
                    print(f"   - Titre: {doc.title}")
                    print(f"   - Type: {doc.doc_type}")
                    print(f"   - Source: {doc.source}")
                    print(f"   - Pays: {doc.country}")
                    print(f"   - Langue: {doc.language}")
                else:
                    print(f"❌ Échec de l'extraction des métadonnées")
                    
            except Exception as e:
                print(f"❌ Erreur lors du traitement: {e}")
        else:
            print(f"⚠️  Fichier manquant pour le document ID {doc.id}")

if __name__ == "__main__":
    from django.db import models
    update_document_metadata()
    print("\n🎉 Mise à jour terminée!")