import requests
import os
import logging

logger = logging.getLogger(__name__)


# intents.py
def fallback_full_intent(question: str) -> str:
    q = (question or "").lower()

    # Indices "liste"
    list_words = ("tous", "toutes", "liste", "affiche", "afficher", "montre", "montrez", "voir", "montrez-moi", "lister")

    # Indices d'attributs (doc/prod) sans exiger les mots "document/produit"
    doc_attr = ("titre", "langue", "version", "source", "pays", "publication", "url", "lien", "métadonneur", "uploadé")
    prod_attr = ("forme", "type", "dosage", "statut", "principe actif", "pa", "site", "zone thérapeutique")

    has_doc_attr = any(k in q for k in doc_attr)
    has_prod_attr = any(k in q for k in prod_attr)
    asks_list = any(w in q for w in list_words)

    if has_doc_attr and not has_prod_attr:
        return "library"
    if has_prod_attr and not has_doc_attr:
        return "product"

    # Relations implicites
    if "lié" in q or "associé" in q or "rattaché" in q:
        # essaie de deviner le sens de la flèche
        # heuristique simple : si on cite un nom de produit connu on ira vers prod_to_doc, sinon doc_to_prod
        return "prod_to_doc"  # on affinera côté parseur

    # Sinon on reste générique
    return "autre"


def detect_full_intent_type(question: str) -> str:
        mistral_key = os.getenv("MISTRAL_API_KEY")
        if not mistral_key:
            logger.warning(f"[FALLBACK] Utilisation du fallback local pour : '{question}'")
            return fallback_full_intent(question)

        prompt = f"""
    Tu es un assistant qui classe une question dans une seule des catégories suivantes :

    - library → la question parle d’un document (notice, fichier, rapport, etc.) ou de ses attributs (titre, langue, type…)
    - product → la question parle d’un médicament, produit ou principe actif et ses attributs (forme, dosage…)
    - prod_to_doc → la question demande à quels documents un produit est lié
    - doc_to_prod → la question demande à quels produits un document est lié
    - autre → la question ne concerne ni un produit ni un document

    Tu dois répondre uniquement avec : library, product, prod_to_doc, doc_to_prod, ou autre.

    Q : {question}  
    →
        """

        try:
            r = requests.post(
                "https://api.mistral.ai/v1/chat/completions",
                headers={
                    "Authorization": f"Bearer {mistral_key}",
                    "Content-Type": "application/json"
                },
                json={
                    "model": "mistral-small",
                    "messages": [
                        {"role": "system", "content": "Tu es un classificateur d'intention. Réponds uniquement avec un mot parmi : library, product, prod_to_doc, doc_to_prod, autre."},
                        {"role": "user", "content": prompt.strip()}
                    ],
                    "temperature": 0.2
                },
                timeout=30
            )
            content = r.json()["choices"][0]["message"]["content"].strip().lower()
            ALLOWED_TYPES = {"library", "product", "prod_to_doc", "doc_to_prod", "autre"}

            if content in ALLOWED_TYPES:
                logger.info(f"[INTENT] ✅ Type détecté par Mistral : '{content}' pour la question : '{question}'")
                return content
            else:
                logger.warning(f"[INTENT] ❌ Type non reconnu par Mistral : '{content}' → Fallback utilisé.")
                return fallback_full_intent(question)

        except Exception as e:
            logger.exception(f"[INTENT] ⚠️ Erreur appel Mistral : {e}")
            return fallback_full_intent(question)
    