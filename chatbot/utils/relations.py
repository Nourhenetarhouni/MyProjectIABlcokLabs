import re
from client.products.models import Product
from chatbot.utils.matching import find_best_product,find_best_document,extract_product_name
import logging
import difflib
logger = logging.getLogger(__name__)



def get_products_linked_to_document(question: str, docs_qs) -> str:
    doc = find_best_document(question, docs_qs)
    if not doc:
        return "Je n’ai pas trouvé ce document. Peux-tu préciser le titre ?"

    produits = Product.objects.filter(source_document=doc)
    if not produits.exists():
        return f"Aucun produit n’est associé au document « {doc.title} »."

    noms = ", ".join(p.name for p in produits)
    return f"Produits associés au document « {doc.title} » : {noms}."



def get_document_linked_to_product(question: str, produits_qs) -> str:
    """
    Gère les questions du type : 'Ce produit est-il lié à un document ?'
    """
    from rawdocs.models import RawDocument  # importer ici si pas encore importé
    from django.db.models import Q

    logger = logging.getLogger(__name__)
    logger.info(f"[Relation] Question reçue pour produit→document : {question}")

    product_name = extract_product_name(question, produits_qs)  # Appel avec deux arguments
    logger.info(f"[Relation] Nom de produit extrait : {product_name}")

    product = find_best_product(product_name, produits_qs)

    if not product:
        logger.warning(f"[Relation] Aucun produit trouvé dans la question : {question}")
        return "Je n’ai pas trouvé ce produit. Peux-tu préciser le nom ?"

    # Rechercher documents associés
    linked_docs = RawDocument.objects.filter(product=product, is_validated=True)

    if not linked_docs.exists():
        return f"Aucun document validé n’est associé au produit « {product.name} »."

    lines = [f"Le produit « {product.name} » est lié aux documents suivants :"]
    for d in linked_docs:
        lines.append(f"- {d.title} ({d.doc_type or 'Type inconnu'})")

    return "\n".join(lines)