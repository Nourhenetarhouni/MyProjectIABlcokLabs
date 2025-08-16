import os
import re
import json
import requests
from pathlib import Path
from datetime import datetime
from urllib.parse import urlparse

import spacy
from PyPDF2 import PdfReader
from langdetect import detect
from dotenv import load_dotenv

# Charger les variables d'environnement depuis .env
load_dotenv()

# Chargez une fois les modèles spaCy :
NLP_FR = spacy.load("fr_core_news_sm")
NLP_EN = spacy.load("en_core_web_sm")

# Stopwords FR/EN basiques pour nettoyage
STOPWORDS = {
    "le", "la", "les", "de", "des", "du", "un", "une", "et", "en", "à", "dans", "que", "qui",
    "pour", "par", "sur", "avec", "au", "aux", "ce", "ces", "se", "ses", "est",
    "the", "and", "of", "to", "in", "that", "it", "is", "was", "for", "on", "are", "with",
    "as", "i", "at", "be", "by", "this"
}


def call_mistral_with_confidence(text_chunk, document_url="", filename=""):
    """
    Get extraction + confidence scores from Mistral in one call.
    La clé API est lue depuis la variable d'environnement MISTRAL_API_KEY.
    """
    api_key = os.getenv(
        "MISTRAL_API_KEY") or "j2wOKpM86nlZhhlvkXXG7rFd4bhM4PN5"  # Fallback à la clé hardcodée si .env non disponible

    try:
        url = "https://api.mistral.ai/v1/chat/completions"
        headers = {
            "Content-Type": "application/json",
            "Authorization": f"Bearer {api_key}"
        }

        prompt = f"""
        You are an expert document analyzer. Analyze this document and extract metadata with confidence scores.

        DOCUMENT TEXT (first 5000 chars):
        {text_chunk[:5000]}

        SOURCE URL: {document_url}
        FILENAME: {filename}

        HINT: Look for version numbers in headers like "DTC_S006597_PF_R_FAB_17319_EN_15.0" where 15.0 is the version

        TASK: Return ONLY a JSON object with extracted metadata AND your confidence scores:

        {{
            "metadata": {{
                "title": "the MAIN document title (not technical headers)",
                "type": "guideline|regulation|directive|report|procedure|standard|manufacturer|certificate|authorization|specifications|other",
                "publication_date": "exact date (DD Month YYYY format)",
                "version": "document version/reference number",
                "source": "organization name",
                "context": "main domain (pharmaceutical, medical, legal, etc.)",
                "country": "country code (EU, US, FR, IE, PL, etc.)",
                "language": "language code (en, fr, etc.)"
            }},
            "confidence_scores": {{
                "title": 85,
                "type": 90,
                "publication_date": 95,
                "version": 20,
                "source": 90,
                "context": 80,
                "country": 95,
                "language": 98
            }},
            "extraction_reasoning": {{
                "title": "Found clear title in document header",
                "type": "Document explicitly mentions 'guideline' in title",
                "publication_date": "Detected header date indicating publication",
                "version": "No clear version number found",
                "source": "URL or internal org name used",
                "context": "Multiple pharmaceutical terms detected",
                "country": "URL domain or regulatory hints used",
                "language": "Detected by language model"
            }}
        }}

        INSTRUCTIONS FOR DOCUMENT TYPE DETECTION:
        - "manufacturer": Documents listing manufacturing sites, manufacturer information, production details
        - "specifications": Documents detailing product specifications, technical specifications, drug product specs
        - "guideline": Official guidance documents from regulatory agencies
        - "regulation": Legal regulatory texts, laws, regulations
        - "directive": EU directives and similar regulatory directives  
        - "report": Assessment reports, evaluation reports, inspection reports
        - "procedure": Standard operating procedures, process descriptions
        - "standard": Technical standards, quality standards
        - "certificate": Certificates, authorizations, approvals
        - "authorization": Marketing authorizations, permits, licenses
        - "other": Any other document type

                
        RULES FOR PUBLICATION DATE DETECTION:
                
        Use the date that appears:
        - At the top near the agency name (e.g. “EMA/CHMP/ICH/24235/2006 Corr.2 23 January 2025” → use 23 January 2025)
        - In the format “Published: ...” or “Publication date: ...”
        - Next to "Official Journal of the European Union" (this is official)

        DO NOT use:
        - “Adopted by CHMP on …”
        - “Date of coming into effect …”
        - “Finalization date”
        - References to old laws like “Directive 2008/57/EC of 15 July 2008”

        Examples:
        ✅ GOOD → “23 January 2025” near header  
        ✅ GOOD → “Published in Official Journal: 2 August 2013”  
        ❌ BAD → “Directive 2008/123/EC of 24 November 2008”  
        ❌ BAD → “Date for coming into effect: 26 July 2023”

        Additional Notes:
        - Prioritize clarity over completeness
        - Return no extra text outside JSON

        TYPE DETECTION KEYWORDS:
        - "SPECIFICATIONS OF" → type: "specifications"
        - "MANUFACTURERS" → type: "manufacturer"  
        - "GUIDELINE" → type: "guideline"
        - "PROCEDURE" → type: "procedure"
        - Look for explicit type indicators in document titles and headers

        INSTRUCTIONS FOR TITLE EXTRACTION:
        - Extract the MAIN document title from the body content, not technical headers
        - Ignore technical codes like "DTC_S006597_PF_R_FAB_17319_EN_15.0"
        - Look for the primary subject/topic in the document body
        - For manufacturer docs: "MANUFACTURERS" + product name + description
        - Combine logical title elements: "MANUFACTURERS S 6597 Film-coated tablet..."
        - Avoid including addresses, company names, or metadata in the title

        INSTRUCTIONS FOR VERSION DETECTION:

        
        1. If a regulatory code is present like:
        - EMA/CHMP/ICH/xxxxx/yyyy
        - ICH/yyyy/stepX
        → extract that full code as version

        2. If "Corr.2", "Rev.1", "(R1)", etc. appears after the code or title → append it

        3. If "Step 5", "Step 2b", etc. appears near the header → append it

        4. Accept also formats like:
        - M4Q(R2) → version = "M4Q(R2)"
        - CTD_QR_Rev.2 → version = "Rev.2"
        - EN_15.0 → version = "15.0"

        — EXAMPLES —
        ✅ EMA/CHMP/ICH/214732/2007 Step 5
        ✅ EMA/CHMP/ICH/24235/2006 Corr.2 Step 5
        ✅ M4Q(R2)
        ✅ Rev. 1
        ✅ Version 3.0

        — DO NOT EXTRACT —
        ❌ Directive 2008/57/EC
        ❌ IDs not linked to versioning


        If no clear version is found, return an empty string: `""`


        INSTRUCTIONS FOR SOURCE DETECTION:
        - Look for explicit organization names in the document
        - Check for regulatory agency indicators (EMA, FDA, ANSM, MHRA, etc.)
        - For manufacturer documents, use the company name mentioned
        - For specifications documents, look for regulatory authority context
        - Check for "European Pharmacopoeia" → likely EMA/European regulatory context
        - If from URL domain: .ema.europa.eu = "EMA", .fda.gov = "FDA", etc.
        - If unclear, analyze content to determine likely source organization
        - Do NOT default to EMA unless clearly an EMA document

        INSTRUCTIONS FOR COUNTRY DETECTION:
        - Look for country-specific indicators in text
        - Check addresses, phone numbers, regulatory codes
        - Analyze URL domain for country hints
        - For manufacturer docs, use country where facilities are located
        - Use specific country codes (FR, IE, PL) not just EU when possible

        CONFIDENCE SCORING:
        - 90-100: Explicitly stated in document
        - 70-89: Strong indicators/evidence  
        - 50-69: Reasonable inference from context
        - 30-49: Weak indicators, uncertain
        - 0-29: Not found or very unclear

        TITLE EXTRACTION EXAMPLES:
        ✅ GOOD: "MANUFACTURERS S 6597 Film-coated tablet containing 10 mg of perindopril arginine and 2.5 mg of indapamide"
        ✅ GOOD: "SPECIFICATIONS OF THE DRUG PRODUCT S 20098 Film-coated tablets containing 25 mg of drug substance"
        ❌ BAD: "DTC_S006597_PF_R_FAB_17319_EN_15.0 MANUFACTURERS S 6597..."
        ❌ BAD: Including addresses or company details in title

        Return ONLY the JSON, no other text.
        """


        data = {
            "model": "mistral-large-latest",
            "messages": [{"role": "user", "content": prompt}],
            "temperature": 0.1,
            "max_tokens": 800
        }

        response = requests.post(url, headers=headers, json=data, timeout=30)
        response.raise_for_status()

        if response.status_code == 200:
            result = response.json()
            response_text = result['choices'][0]['message']['content']

            # Find JSON in response
            json_match = re.search(r'\{.*\}', response_text, re.DOTALL)
            if json_match:
                json_str = json_match.group()
                full_result = json.loads(json_str)
                print("✅ Mistral extraction with confidence successful!")
                return full_result
            else:
                print("❌ No JSON found in Mistral response")
                return None
        else:
            print(f"❌ Mistral API error: {response.status_code}")
            return None

    except Exception as e:
        print(f"❌ Mistral API error: {e}")
        return None


def calculate_overall_quality(confidence_scores):
    """
    Calculate overall extraction quality from LLM confidence scores
    """
    if not confidence_scores:
        return 0

    weights = {
        'title': 1.5,
        'type': 1.2,
        'publication_date': 1.3,
        'source': 1.2,
        'context': 1.0,
        'language': 0.8,
        'country': 0.8,
        'version': 0.7
    }

    total_weighted_score = 0
    total_weight = 0
    for field, score in confidence_scores.items():
        w = weights.get(field, 1.0)
        total_weighted_score += score * w
        total_weight += w

    return int(total_weighted_score / total_weight) if total_weight else 0


import pdfplumber

def extract_full_text(file_path):
    text = ""
    with pdfplumber.open(file_path) as pdf:
        # extraire en priorité les 1ères pages
        for page in pdf.pages[:2]:
            page_text = page.extract_text() or ""
            text += "\n" + page_text
    # ensuite le reste si besoin
    with pdfplumber.open(file_path) as pdf:
        for page in pdf.pages[2:]:
            text += "\n" + (page.extract_text() or "")
    return text


def extract_metadonnees(file_path: str, source_url: str) -> dict:
    """
    Main extraction function with REAL LLM confidence metrics
    """
    print("🔍 Starting LLM extraction with confidence scoring...")
    full_text = extract_full_text(file_path)
    filename = Path(file_path).name
    llm_result = call_mistral_with_confidence(full_text, source_url, filename)

    if llm_result and 'metadata' in llm_result and 'confidence_scores' in llm_result:
        print("✅ Using LLM extraction with real confidence scores!")

        metadata = llm_result['metadata']
        conf_scores = llm_result['confidence_scores']
        reasoning = llm_result.get('extraction_reasoning', {})

        metadata['url_source'] = source_url

        # Calculate quality metrics
        overall_quality = calculate_overall_quality(conf_scores)
        extracted_fields = sum(1 for s in conf_scores.values() if s >= 50)
        total_fields = len(conf_scores)

        metadata['quality'] = {
            'extraction_rate': overall_quality,
            'field_scores': conf_scores,
            'extraction_reasoning': reasoning,
            'extracted_fields': extracted_fields,
            'total_fields': total_fields,
            'llm_powered': True
        }
        return metadata

    # Fallback basic extraction
    print("⚠ LLM extraction failed, using basic fallback")
    return extract_basic_fallback(file_path, source_url)


def extract_basic_fallback(file_path: str, source_url: str) -> dict:
    """Basic fallback with honest low confidence scores"""
    reader = PdfReader(file_path)
    info = reader.metadata or {}
    title = info.title or Path(file_path).stem
    full_text = extract_full_text(file_path)

    try:
        lang = detect(full_text)
    except:
        lang = "en"

    basic_meta = {
        "title": title,
        "type": "unknown",
        "publication_date": "",
        "version": "",
        "source": "",
        "context": "",
        "country": "",
        "language": lang,
        "url_source": source_url
    }

    conf_scores = {
        'title': 30 if title else 0,
        'type': 0,
        'publication_date': 0,
        'version': 0,
        'source': 0,
        'context': 0,
        'country': 0,
        'language': 80 if lang else 0
    }

    overall_quality = calculate_overall_quality(conf_scores)

    basic_meta['quality'] = {
        'extraction_rate': overall_quality,
        'field_scores': conf_scores,
        'extraction_reasoning': {
            'title': 'Basic PDF metadata extraction',
            'type': 'Could not determine document type',
            'source': 'No source identification possible'
        },
        'extracted_fields': 1,
        'total_fields': len(conf_scores),
        'llm_powered': False
    }
    return basic_meta