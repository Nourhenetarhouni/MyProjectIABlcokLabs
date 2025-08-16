
import logging
import re
import difflib
import unicodedata
from rapidfuzz import process, fuzz



logger = logging.getLogger(__name__)
def normalize(s):
    return " ".join(re.findall(r"\w+", (s or "").lower()))



def extract_product_name(question: str, produits_qs) -> str:
    """
    Extrait un nom de produit pertinent depuis la question, avec fuzzy matching sur produits_qs.
    """
    question_cleaned = question.lower().strip(" ?!")

    # Liste des noms de produits disponibles
    produits_names = [p.name.lower() for p in produits_qs]

    # Tentative de fuzzy matching (score > 70 conseillé)
    best_match, score, _ = process.extractOne(question_cleaned, produits_names, scorer=fuzz.ratio)
    if best_match and score >= 70:
        return best_match

    # Fallback simple avec extraction brute si fuzzy ne donne rien de bon
    match = re.search(r"(?:du|de|des|le|la|les|l['’])?\s*([\w\s\-]{3,})", question_cleaned)
    if match:
        return match.group(1).strip()

    return None  # Rien trouvé



def find_best_product(product_name: str, produits_qs) -> object:
    """
    Cherche un produit dans la base en utilisant :
    - match exact ou partiel via __icontains
    - fallback fuzzy matching
    """
    normalized_name = normalize(product_name)
    best, best_score = None, 0.0

    for p in produits_qs:
        name = normalize(p.name)
        if normalized_name in name or name in normalized_name:
            return p  # match direct

        score = difflib.SequenceMatcher(None, normalized_name, name).ratio()
        if score > best_score:
            best, best_score = p, score

    return best if best_score >= 0.45 else None


def find_best_document(title_query: str, queryset):
    q_norm = normalize(title_query)
    best, best_score = None, 0
    for doc in queryset:
        score = difflib.SequenceMatcher(None, q_norm, normalize(doc.title)).ratio()
        if score > best_score:
            best, best_score = doc, score
    return best if best_score >= 0.45 else None
