

# Mapping attributs produits
attr_map_products = {
    "nom": ("name", "Nom du produit"),
    "type": ("form", "Type"),
    "forme": ("form", "Forme"),
    "principe actif": ("active_ingredient", "Principe actif"),
    "dosage": ("dosage", "Dosage"),
    "statut": ("get_status_display", "Statut"),
    "zone thérapeutique": ("therapeutic_area", "Zone thérapeutique"),
    "site": ("sites", "Sites de production"),
}

# mots-clés -> (champ RawDocument, label)
attr_map_library = {
    "source": ("source", "Source"),
    "autorité": ("source", "Source"),
    "authority": ("source", "Source"),
    "contexte": ("context", "Contexte"),
    "context": ("context", "Contexte"),
    "langue": ("language", "Langue"),
    "language": ("language", "Langue"),
    "version": ("version", "Version"),
    "type": ("doc_type", "Type"),
    "pays": ("country", "Pays"),
    "date": ("publication_date", "Date de publication"),
    "url": ("url_source", "URL"),
    "lien": ("url_source", "URL"),
    "publication": ("publication_date", "Date de publication"),
    "date de publication": ("publication_date", "Date de publication"),
    "ajout": ("created_at", "Date d'ajout"),
    "date d'ajout": ("created_at", "Date d'ajout"),
    "validation": ("validated_at", "Statut de validation"),
    "validé": ("validated_at", "Statut de validation"),
    "statut de validation": ("validated_at", "Statut de validation"),
    "date de validation": ("validated_at", "Statut de validation"),
    "uploadé par": ("owner_username", "Uploadé par (Métadonneur)"),
    "qui a uploadé": ("owner_username", "Uploadé par (Métadonneur)"),
    "métadonneur": ("owner_username", "Uploadé par (Métadonneur)"),
}    
        

