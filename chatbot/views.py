from django.http import JsonResponse
from django.views.decorators.csrf import csrf_exempt
import json
import os
import re
import difflib
import datetime
import unicodedata
import logging
import requests
from chatbot.utils.matching import find_best_product, find_best_document
APOST = r"[’']"

# Configuration du logger
logger = logging.getLogger(__name__)

def strip_accents(s: str) -> str:
    return ''.join(c for c in unicodedata.normalize('NFD', s or '') if unicodedata.category(c) != 'Mn')

# Mots déclencheurs pour les listes (élargi)
LIST_WORDS = (
    # conserve les existants et ajoute ces verbes usuels
    "tous", "toutes", "liste", "affiche", "afficher", "montre", "montrez",
    "voir", "lister", "quels", "quelles", "lesquels", "lesquelles",
    "combien", "énumère", "énumérer", "répertorie", "répertorier",
    "donne-moi", "trouve-moi", "cherche", "recherche",
    # [AJOUTS]
    "donner", "donne", "donnez", "fournis", "fournir", "fournissez",
    "recense", "recenser",
    # ajout pour couvrir “disponible(s)”
    "disponible", "disponibles"
)

def should_force_list_mode(entity: str, q_lower: str, filters: dict) -> bool:
    """
    Force le mode 'list' si:
      - entité product + 'produit(s)' dans la question OU présence d'au moins 1 filtre
      - entité library/doc + 'document(s)' dans la question OU présence d'au moins 1 filtre
      - mentions explicites de 'site(s)' pour lister les sites
    """
    if entity == "product" and (re.search(r"\bproduits?\b", q_lower) or filters):
        return True
    if entity in ("library", "document", "doc") and (re.search(r"\bdocuments?\b", q_lower) or filters):
        return True
    if re.search(r"\bsites?\b", q_lower):
        return True
    return False

# Mots interrogatifs qui suggèrent une liste
INTERROGATIVE_LIST_PATTERNS = [
    r"quels?\s+sont\s+les?\s+",
    r"quelles?\s+sont\s+les?\s+",
    r"lesquels?\s+",
    r"lesquelles?\s+",
    r"combien\s+(de|d')?\s+",
    r"y\s+a-t-il\s+",
    r"existe-t-il\s+",
    r"trouve[z]?-moi\s+",
    r"donne[z]?-moi\s+",
    r"cherche[z]?\s+",
    r"recherche[z]?\s+",
]

DOC_FIELD_MAP = {
    "type": "doc_type",
    "source": "source",
    "autorité": "source",
    "authority": "source",
    "langue": "language",
    "language": "language",
    "version": "version",
    "pays": "country",
    "date de publication": "publication_date",
    "publication": "publication_date",
    "date": "publication_date",
    "url": "url_source",
    "lien": "url_source",
    "uploadé par": "owner_username",
    "qui a uploadé": "owner_username",
    "métadonneur": "owner_username",
}

PROD_FIELD_MAP = {
    "type": "form",
    "forme": "form",
    "statut": "status",
    "principe actif": "active_ingredient",
    "dosage": "dosage",
    "nom": "name",
}

# Mapping des valeurs de statut (variations)
STATUS_MAPPING = {
    "arrêté": "arrêté",
    "arrete": "arrêté",
    "arreter": "arrêté",
    "arrêter": "arrêté",
    "en cours d'arrêt": "en cours d'arrêt",
    "cours d'arrêt": "en cours d'arrêt",
    "en cours": "en cours d'arrêt",
    "actif": "actif",
    "active": "actif",
    "approuvé": "approuvé",
    "approuve": "approuvé",
    "validé": "validé",
    "valide": "validé",
    "suspendu": "suspendu",
    "rejeté": "rejeté",
    "rejete": "rejeté",
}

# --- [AJOUT] normalisation apostrophes/quotes ---
APOST = r"[’']"  # accepte ' et ’

def normalize_punct(s: str) -> str:
    # Uniformise les apostrophes et guillemets “curly”
    return (s or "").replace("’", "'").replace("‘", "'").replace("`", "'") \
                    .replace("“", '"').replace("”", '"')

# --- [REMPLACE] ancien STATUS_MAPPING par cette version robuste ---
_RAW_STATUS_MAPPING = {
    # Arrêté / en arrêt
    "arrêté": "arrêté",
    "arrete": "arrêté",
    "arrêter": "arrêté",
    "arreter": "arrêté",
    # En cours d'arrêt
    "en cours d'arrêt": "en cours d'arrêt",
    "en cours d'arret": "en cours d'arrêt",
    "cours d'arrêt": "en cours d'arrêt",
    "cours d'arret": "en cours d'arrêt",
    "en cours": "en cours d'arrêt",
    # Autres statuts courants (à garder si ta base les supporte)
    "actif": "actif",
    "active": "actif",
    "approuvé": "approuvé",
    "approuve": "approuvé",
    "validé": "validé",
    "valide": "validé",
    "suspendu": "suspendu",
    "rejeté": "rejeté",
    "rejete": "rejeté",
}

STATUS_MAPPING = {
    # Clés normalisées (accents enlevés + apostrophes uniformisées)
    strip_accents(normalize_punct(k)).lower(): v
    for k, v in _RAW_STATUS_MAPPING.items()
}

# --- [REMPLACE/ADAPTE] ta fonction de normalisation de filtres ---
def normalize_filter_value(field: str, value: str) -> str:
    """
    Normalise une valeur de filtre utilisateur (ponctuation, accents, casse).
    Ajuste aussi les synonymes / variantes par champ (ex: status).
    """
    v = strip_accents(normalize_punct(value)).lower().strip()

    if field in ("status", "statut"):
        # Map sur clés normalisées
        return STATUS_MAPPING.get(v, value)

    # Laisse le comportement existant pour les autres champs
    return value


from rapidfuzz import process, fuzz

QUOTES_RE = r"[\"'«»""'']"

def _extract_quoted(text: str) -> list[str]:
    return re.findall(rf"{QUOTES_RE}([^\"'«»""'']+){QUOTES_RE}", text)

def _guess_fields(q_lower: str, alias_map: dict, threshold: int = 85) -> list[str]:
    fields = set()
    aliases = list(alias_map.keys())
    candidates = re.findall(r"\w{3,}", q_lower)
    
    for n in (2, 3):
        for i in range(len(candidates) - n + 1):
            candidates.append(" ".join(candidates[i:i+n]))
    
    for cand in set(candidates):
        match = process.extractOne(cand, aliases, scorer=fuzz.token_set_ratio)
        if match and match[1] >= threshold:
            fields.add(alias_map[match[0]])
    
    return list(fields)

def _is_list_request(question: str) -> bool:
    """Détecte si la question demande une liste de résultats"""
    q_lower = question.lower()
    
    # Vérification des mots déclencheurs explicites
    if any(word in q_lower for word in LIST_WORDS):
        return True
    
    # Vérification des patterns interrogatifs
    for pattern in INTERROGATIVE_LIST_PATTERNS:
        if re.search(pattern, q_lower):
            return True
    
    # Patterns spécifiques pour les pluriels
    plural_patterns = [
        r"les\s+\w+",
        r"des\s+\w+", 
        r"\w+s\s+(avec|de|du|dans|en|par)",
        r"produits?\s+",
        r"documents?\s+",
        r"sites?\s+",
    ]
    
    for pattern in plural_patterns:
        if re.search(pattern, q_lower):
            return True
    
    return False

def _best_entity_for_name(name_hint: str, produits_qs, docs_qs):
    if not name_hint:
        return None, None
    
    best_prod = find_best_product(name_hint, produits_qs)
    best_doc = find_best_document(name_hint, docs_qs)

    def _sim(a, b):
        if not a or not b:
            return 0.0
        return difflib.SequenceMatcher(None, str(a).lower(), str(b).lower()).ratio()

    sp = _sim(name_hint, getattr(best_prod, "name", ""))
    sd = _sim(name_hint, getattr(best_doc, "title", ""))
    
    if sp == 0 and sd == 0:
        return None, None
    
    return ("product", best_prod) if sp >= sd else ("library", best_doc)

# Patterns de filtres améliorés
DOC_TRIGGER_MAP = {
    "type": "doc_type",
    "langue": "language",
    "source": "source",
    "pays": "country",
    "version": "version",
}

PROD_TRIGGER_MAP = {
    "type": "form", "forme": "form",
    "statut": "status",
    "principe actif": "active_ingredient", "pa": "active_ingredient",
    "dosage": "dosage",
}

_QUOTED_VAL = r"['\"«»""'']?([^'\"«»""'';,]+)['\"«»""'']?"

DOC_FILTER_PATTERNS = [
    (re.compile(rf"(?:de|du|d{APOST})\s*type\s+{_QUOTED_VAL}", re.I), "type"),
    (re.compile(rf"type\s*[:=]\s*{_QUOTED_VAL}", re.I), "type"),
    (re.compile(rf"(?:en|de)\s*langue\s+{_QUOTED_VAL}", re.I), "langue"),
    (re.compile(rf"langue\s*[:=]\s*{_QUOTED_VAL}", re.I), "langue"),
    (re.compile(rf"(?:de|la)\s*source\s+{_QUOTED_VAL}", re.I), "source"),
    (re.compile(rf"source\s*[:=]\s*{_QUOTED_VAL}", re.I), "source"),
    (re.compile(rf"(?:au|du|de)\s*pays\s+{_QUOTED_VAL}", re.I), "pays"),
    (re.compile(rf"pays\s*[:=]\s*{_QUOTED_VAL}", re.I), "pays"),
    (re.compile(rf"(?:en|de)\s*version\s+{_QUOTED_VAL}", re.I), "version"),
    (re.compile(rf"version\s*[:=]\s*{_QUOTED_VAL}", re.I), "version"),
]

PROD_FILTER_PATTERNS = [
    (re.compile(rf"(?:de|du|d{APOST})\s*(?:type|forme)\s+{_QUOTED_VAL}", re.I), "type"),
    (re.compile(rf"(?:type|forme)\s*[:=]\s*{_QUOTED_VAL}", re.I), "type"),
    (re.compile(rf"(?:avec|ayant|de|du)\s*statut\s*{_QUOTED_VAL}", re.I), "statut"),
    (re.compile(rf"statut\s*[:=]?\s*{_QUOTED_VAL}", re.I), "statut"),
    (re.compile(rf"en\s+cours\s+d{APOST}arr[ée]t", re.I), "statut", "en cours d'arrêt"),
    (re.compile(rf"arrêtés?", re.I), "statut", "arrêté"),
    (re.compile(rf"(?:principe\s+actif|pa)\s*[:=]?\s*{_QUOTED_VAL}", re.I), "principe actif"),
    (re.compile(rf"dosage\s*[:=]?\s*{_QUOTED_VAL}", re.I), "dosage"),
]

def _extract_filters(q: str, entity: str):
    """Extraction améliorée des filtres avec gestion des statuts spéciaux"""
    filters = []
    text = q or ""
    patterns = DOC_FILTER_PATTERNS if entity == "library" else PROD_FILTER_PATTERNS
    trigger_map = DOC_TRIGGER_MAP if entity == "library" else PROD_TRIGGER_MAP

    for pattern_info in patterns:
        if len(pattern_info) == 3:  # Pattern avec valeur prédéfinie
            rgx, key, predefined_value = pattern_info
            if rgx.search(text):
                field = trigger_map.get(key, key)
                filters.append((field, predefined_value))
        else:
            rgx, key = pattern_info
            m = rgx.search(text)
            if m:
                raw_val = (m.group(1) or "").strip()
                field = trigger_map.get(key, key)
                filters.append((field, raw_val))

    return filters

def _detect_entity_from_context(question: str, produits_qs, docs_qs) -> str:
    """Détection intelligente de l'entité basée sur le contexte"""
    q_lower = question.lower()
    
    # Mots-clés spécifiques aux produits
    product_keywords = [
        "produit", "médicament", "principe actif", "dosage", "statut", "forme",
        "sirop", "comprimé", "gélule", "injection", "arrêté", "actif", "suspendu"
    ]
    
    # Mots-clés spécifiques aux documents
    doc_keywords = [
        "document", "fichier", "rapport", "guide", "guideline", "version",
        "langue", "source", "publication", "uploadé", "validé"
    ]
    
    # Mots-clés spécifiques aux sites
    site_keywords = [
        "site", "usine", "manufacture", "fabrication", "adresse", "lieu",
        "emplacement", "paris", "berlin", "amsterdam", "galway"
    ]
    
    product_score = sum(1 for keyword in product_keywords if keyword in q_lower)
    doc_score = sum(1 for keyword in doc_keywords if keyword in q_lower)
    site_score = sum(1 for keyword in site_keywords if keyword in q_lower)
    
    # Détection spéciale pour les sites
    if site_score > 0 or "site" in q_lower:
        return "sites"
    
    if product_score > doc_score:
        return "product"
    elif doc_score > 0:
        return "library"
    
    return None

def parse_request(question: str, intent: str, produits_qs, docs_qs):
    """Analyse améliorée de la requête"""
    q = question or ""
    ql = q.lower()

    # Détection améliorée des listes
    wants_list = _is_list_request(q)
    
    fields_doc = _guess_fields(ql, DOC_FIELD_MAP)
    fields_prod = _guess_fields(ql, PROD_FIELD_MAP)

    quoted_candidates = _extract_quoted(q)
    name_or_title_hint = quoted_candidates[0].strip() if quoted_candidates else None
    
    if not name_or_title_hint:
        m = re.search(r"(?:de|du|des|la|le|l[''])\s+(.+?)(?:\?|\.|,|;|$)", q, flags=re.IGNORECASE)
        if m:
            name_or_title_hint = m.group(1).strip()

    # Détection intelligente de l'entité
    entity = _detect_entity_from_context(q, produits_qs, docs_qs)
    
    if not entity:
        if fields_doc and not fields_prod:
            entity = "library"
        elif fields_prod and not fields_doc:
            entity = "product"
        else:
            entity, _ = _best_entity_for_name(name_or_title_hint, produits_qs, docs_qs)

    if not entity and intent:
        entity = "library" if intent == "library" else "product" if intent == "product" else None

    # Extraction des filtres
    filters = _extract_filters(q, entity) if entity else []

    fields = fields_doc if entity == "library" else fields_prod if entity == "product" else []
    title = name = None
    
    if entity == "library":
        title = name_or_title_hint
    elif entity == "product":
        name = name_or_title_hint

    mode = "list" if wants_list else "detail"
    # ⚠️ correction: utiliser ql ici (et non q_lower qui n’existe pas dans cette portée)
    if should_force_list_mode(entity, ql, filters):
        mode = "list"
        
    return {
        "entity": entity, 
        "mode": mode, 
        "filters": filters, 
        "fields": fields, 
        "title": title, 
        "name": name
    }

def list_documents(qs, filters, clean, format_date, as_md):
    """Liste des documents avec filtrage amélioré"""
    for field, value in filters:
        normalized_value = normalize_filter_value(field, value)
        q1 = qs.filter(**{f"{field}__iexact": normalized_value})
        qs = q1 if q1.exists() else qs.filter(**{f"{field}__icontains": normalized_value})
    
    cols = ["Titre", "Type", "Langue", "Version", "Source", "Date de publication", "Pays"]
    rows = [{
        "Titre": clean(d.title),
        "Type": clean(getattr(d, "doc_type", "")),
        "Langue": clean(d.language or ""),
        "Version": clean(d.version or ""),
        "Source": clean(d.source or ""),
        "Date de publication": format_date(d.publication_date),
        "Pays": clean(d.country or ""),
    } for d in qs]
    
    return as_md(rows, cols, empty_msg="Aucun document trouvé.")

def list_products(qs, filters, clean, as_md):
    """Liste des produits avec filtrage amélioré"""
    for field, value in filters:
        normalized_value = normalize_filter_value(field, value)
        
        if field == "status":
            # Recherche flexible pour les statuts
            status_queries = [
                qs.filter(status__iexact=normalized_value),
                qs.filter(status__icontains=normalized_value),
            ]
            
            # Gestion spéciale pour "en cours d'arrêt"
            if "cours" in normalized_value.lower() or "arrêt" in normalized_value.lower():
                status_queries.append(qs.filter(status__icontains="cours"))
                status_queries.append(qs.filter(status__icontains="arrêt"))
            
            for query in status_queries:
                if query.exists():
                    qs = query
                    break
        else:
            q1 = qs.filter(**{f"{field}__iexact": normalized_value})
            qs = q1 if q1.exists() else qs.filter(**{f"{field}__icontains": normalized_value})
    
    cols = ["Nom", "Type", "Principe actif", "Dosage", "Statut"]
    rows = [{
        "Nom": clean(p.name),
        "Type": clean(p.form),
        "Principe actif": clean(p.active_ingredient or ""),
        "Dosage": clean(p.dosage or ""),
        "Statut": clean(p.get_status_display()),
    } for p in qs]
    
    return as_md(rows, cols, empty_msg="Aucun produit trouvé.")

def list_sites(produits_qs, clean, as_md):
    """Liste tous les sites disponibles"""
    sites = []
    
    for p in produits_qs:
        for site in p.sites.all():
            sites.append({
                "Nom du site": clean(getattr(site, 'site_name', 'Non spécifié')),
                "Ville": clean(getattr(site, 'city', 'Non spécifiée')),
                "Pays": clean(getattr(site, 'country', 'Non spécifié')),
                "Adresse": clean(getattr(site, 'address', 'Non spécifiée')),
                "Produit associé": clean(p.name),
            })
    
    if not sites:
        return "Aucun site trouvé dans la base de données."
    
    cols = ["Nom du site", "Ville", "Pays", "Adresse", "Produit associé"]
    return as_md(sites, cols, empty_msg="Aucun site trouvé.")

def detail_document(qs, fields, title_hint, raw_q, clean, format_date):
    """Détail d'un document spécifique"""
    doc = find_best_document(title_hint or raw_q, qs)
    if not doc:
        return "Je n'ai pas trouvé ce document. Peux-tu préciser le titre ?"
    
    if not fields:
        return (
            f"Titre : {clean(doc.title)}\n"
            f"Type : {clean(getattr(doc, 'doc_type', ''))}\n"
            f"Langue : {clean(getattr(doc, 'language', ''))}\n"
            f"Version : {clean(getattr(doc, 'version', ''))}\n"
            f"Source : {clean(getattr(doc, 'source', ''))}\n"
            f"Date de publication : {format_date(getattr(doc, 'publication_date', ''))}\n"
            f"Pays : {clean(getattr(doc, 'country', ''))}\n"
            f"Uploadé par : {clean(getattr(getattr(doc, 'owner', None), 'username', 'non spécifié'))}"
        )
    
    parts = []
    for f in fields:
        if f == "owner_username":
            val = getattr(getattr(doc, "owner", None), "username", "non spécifié")
        else:
            val = getattr(doc, f, "")
            if f in ("publication_date", "validated_at", "created_at"):
                val = format_date(val)
        parts.append(f"{f.replace('_', ' ').title()} : {clean(val)}")
    
    return f"{' ; '.join(parts)} du document « {doc.title} »."

def detail_product(qs, fields, name_hint, raw_q, clean):
    """Détail d'un produit spécifique"""
    prod = find_best_product(name_hint or raw_q, qs)
    if not prod:
        return "Je n'ai pas trouvé ce produit. Peux-tu préciser le nom ?"
    
    if not fields:
        return (
            f"Nom : {clean(prod.name)}\n"
            f"Type : {clean(prod.form)}\n"
            f"Principe actif : {clean(prod.active_ingredient)}\n"
            f"Dosage : {clean(prod.dosage)}\n"
            f"Statut : {clean(prod.get_status_display())}"
        )
    
    parts = []
    for f in fields:
        if f == "status":
            val = prod.get_status_display()
        elif f == "sites":
            val = "; ".join(f"{s.site_name} ({s.country})" for s in prod.sites.all()) or "non spécifié"
        else:
            val = getattr(prod, f, "")
        parts.append(f"{f.replace('_', ' ').title()} : {clean(val)}")
    
    return f"{' ; '.join(parts)} du produit « {prod.name} »."

def as_md(rows, cols, empty_msg="Aucun résultat."):
    """Génération de tableaux Markdown"""
    if not rows:
        return empty_msg
    
    head = "| " + " | ".join(cols) + " |"
    sep = "| " + " | ".join(["---"] * len(cols)) + " |"
    lines = [head, sep]
    
    for r in rows:
        lines.append("| " + " | ".join(r.get(c, "") for c in cols) + " |")
    
    return "\n".join(lines)

@csrf_exempt
def chatbot_api(request):
    """
    Chatbot API amélioré avec détection intelligente des intentions
    """
    if request.method != 'POST':
        return JsonResponse({'response': 'Méthode non autorisée.'}, status=405)

    try:
        data = json.loads(request.body)
    except json.JSONDecodeError:
        return JsonResponse({'response': 'Requête invalide (JSON mal formé).'}, status=400)

    question = (data.get('message') or '').strip()
    q_lower = question.lower()

    # Imports des modèles
    from client.products.models import Product
    from rawdocs.models import RawDocument

    produits_qs = Product.objects.all()
    docs_qs = RawDocument.objects.filter(is_validated=True).select_related('owner')

    # Fonctions utilitaires
    def clean(v):
        v = '' if v is None else str(v).strip()
        return v if v and v != 'N/A' else 'non spécifié'

    def format_date(val):
        if not val:
            return 'non spécifiée'
        if isinstance(val, (datetime.date, datetime.datetime)):
            return val.strftime('%Y-%m-%d')
        s = str(val).strip()
        for f in ('%Y-%m-%d', '%d/%m/%Y', '%d-%m-%Y', '%Y/%m/%d'):
            try:
                return datetime.datetime.strptime(s, f).strftime('%Y-%m-%d')
            except Exception:
                continue
        return s

    # Détection du type de question
    from chatbot.utils.intents import detect_full_intent_type

    mistral_key = os.environ.get('MISTRAL_API_KEY')
    if not mistral_key:
        logger.warning("Clé Mistral manquante – fallback règles.")
        question_type = _detect_entity_from_context(question, produits_qs, docs_qs)
    else:
        question_type = detect_full_intent_type(question)

    logger.info(f"[DEBUG] Type détecté : '{question_type}' pour : '{question}'")

    # Gestion spéciale pour les sites
    # ⚠️ assouplissement: si la question mentionne “site(s)”, on liste directement
    if "site" in q_lower:
        response = list_sites(produits_qs, clean, as_md)
        return JsonResponse({'response': response})

    # Relations entre entités
    from chatbot.utils.relations import get_products_linked_to_document, get_document_linked_to_product

    if question_type == "prod_to_doc":
        response = get_document_linked_to_product(question, produits_qs)
        return JsonResponse({'response': response})

    if question_type == "doc_to_prod":
        response = get_products_linked_to_document(question, docs_qs)
        return JsonResponse({'response': response})

    # Analyse de la requête
    parsed = parse_request(question, question_type, produits_qs, docs_qs)
    logger.debug(f"[PARSED] {parsed}")

    # Traitement des réponses
    if parsed["entity"] == "library":
        if parsed["mode"] == "list":
            table = list_documents(docs_qs, parsed["filters"], clean, format_date, as_md)
            return JsonResponse({"response": table})
        else:
            txt = detail_document(docs_qs, parsed["fields"], parsed["title"], question, clean, format_date)
            return JsonResponse({"response": txt})

    if parsed["entity"] == "product":
        if parsed["mode"] == "list":
            table = list_products(produits_qs, parsed["filters"], clean, as_md)
            return JsonResponse({"response": table})
        else:
            txt = detail_product(produits_qs, parsed["fields"], parsed["name"], question, clean)
            return JsonResponse({"response": txt})

    # Fallback avec contexte
    produits_str = ''
    for p in produits_qs:
        sites = p.sites.all()
        sites_str = ', '.join([f"{s.site_name} ({s.city}, {s.country})" for s in sites]) if sites else 'Aucun'
        produits_str += (
            f"- Nom: {clean(p.name)} | Statut: {clean(p.get_status_display())} | "
            f"PA: {clean(getattr(p, 'active_ingredient', None))} | "
            f"Dosage: {clean(getattr(p, 'dosage', None))} | "
            f"Forme: {clean(getattr(p, 'form', None))} | "
            f"Sites: {sites_str}\n"
        )

    docs_str = ''
    for d in docs_qs:
        docs_str += (
            f"- {clean(d.title)} | {clean(getattr(d, 'doc_type', ''))} | "
            f"{clean(getattr(d, 'language', ''))} | Source: {clean(getattr(d, 'source', ''))}\n"
        )

    contexte = (
        f"Voici un résumé des données:\n\n"
        f"Produits:\n{produits_str}\n"
        f"Documents validés:\n{docs_str}\n"
    )

    if mistral_key:
        content = call_mistral(question, contexte, mistral_key)
        logger.info(f"Fallback Mistral pour : '{question}'")
        return JsonResponse({'response': content})
    else:
        logger.info("Réponse générique - entité non détectée")
        return JsonResponse({'response': "Je n'ai pas bien compris votre demande. Pouvez-vous reformuler en précisant si vous cherchez des informations sur des produits, des documents ou des sites ?"})

def call_mistral(question: str, contexte: str, api_key: str) -> str:
    """Appel à l'API Mistral pour les cas non couverts"""
    prompt = (
        contexte
        + f"\n\nQuestion utilisateur : {question}\n"
        "Consignes : Réponds uniquement selon les données ci-dessus. "
        "Réponds de manière professionnelle et précise. Utilise un tableau Markdown "
        "si la réponse concerne plusieurs éléments."
    )
    
    try:
        r = requests.post(
            "https://api.mistral.ai/v1/chat/completions",
            headers={"Authorization": f"Bearer {api_key}", "Content-Type": "application/json"},
            json={
                "model": "mistral-small",
                "messages": [
                    {"role": "system",
                     "content": "Tu es un assistant professionnel pour une base de données pharmaceutique. "
                               "Réponds de manière précise et structurée selon le contexte fourni."},
                    {"role": "user", "content": prompt}
                ],
                "temperature": 0.3
            },
            timeout=60
        )
        
        if r.status_code == 200:
            content = r.json().get('choices', [{}])[0].get('message', {}).get('content', '').strip()
            return content or "Je n'ai pas pu traiter votre demande."
        
        logger.error(f"Erreur Mistral API: {r.status_code} - {r.text}")
        return "Une erreur s'est produite lors du traitement de votre demande."
        
    except Exception as e:
        logger.exception(f"Erreur dans call_mistral: {str(e)}")
        return "Une erreur technique s'est produite. Veuillez réessayer."
