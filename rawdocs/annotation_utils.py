# rawdocs/annotation_utils.py

import re
import json
import requests
from typing import List, Dict, Tuple
from PyPDF2 import PdfReader


def extract_pages_from_pdf(file_path: str) -> List[str]:
    """Extract text from each page of the PDF"""
    reader = PdfReader(file_path)
    pages = []

    for page_num, page in enumerate(reader.pages, 1):
        page_text = page.extract_text() or ""
        # Clean text but preserve structure
        page_text = re.sub(r'\s+', ' ', page_text).strip()
        pages.append(page_text)

    return pages


def call_mistral_annotation(page_text: str, page_number: int) -> List[Dict]:
    """
    Enhanced Mistral annotation with more aggressive detection
    """
    MISTRAL_API_KEY = "oKdjCl98ACUqpUc4TCyqcfZFMzNNdapl"

    try:
        url = "https://api.mistral.ai/v1/chat/completions"

        headers = {
            "Content-Type": "application/json",
            "Authorization": f"Bearer {MISTRAL_API_KEY}"
        }

        # FRENCH-AWARE aggressive prompt for MORE annotations
        prompt = f"""
        You are an expert pharmaceutical regulatory analyst specializing in FRENCH and EU regulatory documents. Your task is to find EVERY SINGLE regulatory entity in this text. The text is in FRENCH. Be VERY thorough and find ALL entities.

        TEXT TO ANALYZE (FRENCH):
        {page_text}

        FIND ALL THESE ENTITIES (French and English terms):

        1. PROCEDURE_TYPE: 
           - French: "Type IA", "Type IB", "Type II", "notification de type IA/IB/II"
           - English: "IA", "IB", "II", "minor variation", "major variation"
           - "procédure centralisée", "centralised procedure", "MAA", "PSUR"

        2. DELAY:
           - French: "immédiatement", "au moment de", "au terme de", "dans les X jours"
           - English: "30 days", "within 6 months", "Day 30", "immediately"
           - ANY time reference in French or English

        3. AUTHORITY:
           - "EMA", "FDA", "CHMP", "PRAC", "autorités compétentes"
           - "État membre de référence", "reference Member State"
           - "autorité compétente nationale", "competent authority"

        4. LEGAL_REFERENCE:
           - "Article X", "Annexe I/II/III", "ICH/VICH"
           - "lignes directrices applicables", "guidelines"
           - "résumé des caractéristiques du produit"
           - "Règlement", "Directive", ANY legal reference

        5. REQUIRED_CONDITION:
           - Look for "Conditions à remplir" or "Conditions" sections
           - Find numbered items like "1. La nouvelle taille...", "2. Le matériau..."
           - French obligation words: "doit", "requise", "nécessaire"
           - Complete sentences that are requirements/conditions

        6. REQUIRED_DOCUMENT:
           - Look for "Documents à fournir" or "Documents" sections
           - Find numbered items like "1. Version modifiée...", "2. Justification..."
           - "dossier", "études", "déclaration", "justification"
           - "échantillons", "données", Complete document requirements

        CRITICAL FRENCH CONTEXT:
        - "Conditions à remplir" = Conditions section - extract numbered items
        - "Documents à fournir" = Documents section - extract numbered items  
        - "doit" = must/shall - indicates condition
        - "immédiatement" = immediately - is a delay
        - "autorités compétentes" = competent authorities

        SPECIAL INSTRUCTION FOR STRUCTURED LISTS:
        When you see "Conditions:" or "Documents:" followed by numbered lists (1., 2., 3.), 
        extract EACH numbered item as a separate entity of the appropriate type.

        Return JSON with EXACT character positions:
        [
            {{
                "text": "exact French text found",
                "start_pos": 123,
                "end_pos": 130,
                "type": "procedure_type|delay|authority|legal_reference|required_condition|required_document",
                "confidence": 0.75,
                "reasoning": "French regulatory analysis: this is a [type] because..."
            }}
        ]

        BE THOROUGH with French text. Find MORE entities rather than fewer. Return ONLY the JSON array.
        """

        data = {
            "model": "mistral-large-latest",
            "messages": [{"role": "user", "content": prompt}],
            "temperature": 0.3,  # Slightly higher for more creativity
            "max_tokens": 2500  # More tokens for more annotations
        }

        response = requests.post(url, headers=headers, json=data, timeout=60)

        if response.status_code == 200:
            result = response.json()
            response_text = result['choices'][0]['message']['content']

            print(f"🔍 Mistral response for page {page_number}:")
            print(f"Raw response length: {len(response_text)} characters")
            print(f"First 500 chars: {response_text[:500]}...")

            try:
                # Extract JSON from response
                # Extract JSON from response (handle code blocks)
                # First try to extract from ```json blocks
                json_match = re.search(r'```json\s*(\[.*?\])\s*```', response_text, re.DOTALL)
                if json_match:
                    json_str = json_match.group(1)
                else:
                    # Fallback to direct JSON extraction
                    json_match = re.search(r'\[.*?\]', response_text, re.DOTALL)
                    if json_match:
                        json_str = json_match.group()
                    else:
                        json_str = None

                if json_str:
                    print(f"📝 Found JSON: {len(json_str)} characters")

                    ai_annotations = json.loads(json_str)
                    print(f"🎯 Mistral found {len(ai_annotations)} raw annotations")

                    # Validate AI annotations with DEBUG info
                    valid_annotations = []
                    for i, ann in enumerate(ai_annotations):
                        if (isinstance(ann, dict) and
                                all(k in ann for k in
                                    ['text', 'start_pos', 'end_pos', 'type', 'confidence', 'reasoning'])):
                            valid_annotations.append(ann)
                            print(f"  ✅ Valid annotation {i + 1}: {ann['type']} - '{ann['text'][:30]}...'")
                        else:
                            print(f"  ❌ Invalid annotation {i + 1}: {ann}")

                    print(f"✅ {len(valid_annotations)} valid annotations after validation")
                    # DEBUG: Show what LLM actually found
                    for ann in valid_annotations:
                        print(f"  🔍 LLM found: {ann['type']} - '{ann['text']}'")
                    # Validate positions with DEBUG
                    validated = validate_annotation_positions(page_text, valid_annotations)
                    # DEBUG: Show what was filtered out
                    filtered_count = len(annotations) - len(validated)
                    if filtered_count > 0:
                        print(f"⚠️  {filtered_count} annotations were filtered out during position validation")
                    print(f"📍 {len(validated)} annotations after position validation")

                    # Add MORE aggressive pattern detection
                    pattern_entities = find_aggressive_patterns(page_text)
                    print(f"🔍 Pattern detection found {len(pattern_entities)} additional entities")

                    # Combine results
                    combined = combine_llm_and_patterns(validated, pattern_entities, page_text)
                    print(f"🎉 FINAL RESULT: {len(combined)} total annotations")

                    # Debug: show what types were found
                    type_counts = {}
                    for ann in combined:
                        type_counts[ann['type']] = type_counts.get(ann['type'], 0) + 1
                    print(f"📊 Types found: {type_counts}")

                    return combined

                else:
                    print(f"❌ No JSON found in Mistral response")
                    print(f"Response was: {response_text}")
                    return find_aggressive_patterns(page_text)

            except json.JSONDecodeError as e:
                print(f"❌ JSON parse error: {e}")
                print(f"Attempted to parse: {json_str[:200]}...")
                return find_aggressive_patterns(page_text)

        elif response.status_code == 429:
            print(f"🚫 Rate limit hit for page {page_number}")
            return find_aggressive_patterns(page_text)
        else:
            print(f"❌ Mistral API error {response.status_code}: {response.text}")
            return find_aggressive_patterns(page_text)

    except Exception as e:
        print(f"❌ Error calling Mistral: {e}")
        return find_aggressive_patterns(page_text)


def find_structured_french_entities(text: str) -> List[Dict]:
    """
    Special function to find structured French conditions and documents
    """
    entities = []

    # Find CONDITIONS sections and extract numbered items
    conditions_pattern = r'(Conditions?\s+à\s+remplir|Conditions?)\s*:?\s*(.*?)(?=Documents?|Type\s+de\s+procédure|$)'
    conditions_matches = re.finditer(conditions_pattern, text, re.IGNORECASE | re.DOTALL)

    for match in conditions_matches:
        conditions_section = match.group(2)
        section_start = match.start(2)

        # Find numbered items in conditions section
        numbered_items = re.finditer(r'(\d+\.\s+[^0-9]+?)(?=\d+\.|$)', conditions_section, re.DOTALL)

        for item_match in numbered_items:
            item_text = item_match.group(1).strip()
            if len(item_text) > 20:  # Only meaningful conditions
                entities.append({
                    'text': item_text,
                    'start_pos': section_start + item_match.start(),
                    'end_pos': section_start + item_match.end(),
                    'type': 'required_condition',
                    'confidence': 0.95,
                    'reasoning': 'Structured French condition from "Conditions" section'
                })

    # Find DOCUMENTS sections and extract numbered items
    documents_pattern = r'(Documents?\s+à\s+fournir|Documents?)\s*:?\s*(.*?)(?=Note|Conditions?|Type\s+de\s+procédure|$)'
    documents_matches = re.finditer(documents_pattern, text, re.IGNORECASE | re.DOTALL)

    for match in documents_matches:
        documents_section = match.group(2)
        section_start = match.start(2)

        # Find numbered items in documents section
        numbered_items = re.finditer(r'(\d+\.\s+[^0-9]+?)(?=\d+\.|$)', documents_section, re.DOTALL)

        for item_match in numbered_items:
            item_text = item_match.group(1).strip()
            if len(item_text) > 20:  # Only meaningful documents
                entities.append({
                    'text': item_text,
                    'start_pos': section_start + item_match.start(),
                    'end_pos': section_start + item_match.end(),
                    'type': 'required_document',
                    'confidence': 0.95,
                    'reasoning': 'Structured French document from "Documents" section'
                })

    print(f"🇫🇷 Structured French detection found {len(entities)} conditions/documents")
    return entities


def find_aggressive_patterns(text: str) -> List[Dict]:
    """
    FRENCH-AWARE aggressive pattern detection - find everything!
    """
    entities = []

    # FRENCH and ENGLISH comprehensive patterns
    aggressive_patterns = [
        # Procedure types - French and English
        (r'\bType\s+(IA|IB|II)\b', 'procedure_type', 0.95),
        (r'\bnotification\s+de\s+type\s+(IA|IB|II)\b', 'procedure_type', 0.95),
        (r'\b(IA|IB|II)\s+(?:variation|IN)\b', 'procedure_type', 0.9),
        (r'\b(IA|IB|II)\b(?!\s+(?:to|the|and|or|is|are|will|can|may|of|in|on|at|by|for|dans|de|du|le|la|les|et|ou|est|sont|avec))',
         'procedure_type', 0.85),
        (r'\b(variation\s+mineure|variation\s+majeure|minor\s+variation|major\s+variation)\b', 'procedure_type', 0.9),
        (r'\b(procédure\s+centralisée|centralised\s+procedure|mutual\s+recognition|national\s+procedure)\b',
         'procedure_type', 0.9),
        (r'\b(MAA|PSUR|PBRER|CCDS)\b', 'procedure_type', 0.85),

        # Delays - French time expressions
        (r'\b(immédiatement|immediately)\b', 'delay', 0.95),
        (r'\bau\s+moment\s+de\s+(?:la\s+)?(mise\s+en\s+œuvre|soumission)', 'delay', 0.9),
        (r'\bau\s+terme\s+de\s+(?:la\s+)?[^.]{5,50}', 'delay', 0.85),
        (r'\bdans\s+les\s+(\d{1,3}\s+jours?)', 'delay', 0.95),
        (r'\bwithin\s+(\d{1,3}\s+(?:days?|months?|jours?|mois))', 'delay', 0.95),
        (r'\bby\s+[Dd]ay\s+(\d{1,3})', 'delay', 0.95),
        (r'\b(\d{1,3}\s+(?:days?|months?|years?|jours?|mois|années?))', 'delay', 0.8),

        # Authorities - French and English
        (r'\b(EMA|FDA|CHMP|PRAC|CAT|PDCO)\b', 'authority', 0.95),
        (r'\b(autorités?\s+compétentes?)\b', 'authority', 0.95),
        (r'\b([Rr]eference\s+[Mm]ember\s+[Ss]tate|État\s+membre\s+de\s+référence)', 'authority', 0.9),
        (r'\b([Cc]oncerned\s+[Mm]ember\s+[Ss]tate|États?\s+membres?\s+concernés?)', 'authority', 0.9),
        (r'\b([Mm]ember\s+[Ss]tate|États?\s+membres?)\b', 'authority', 0.8),
        (r'\b([Nn]ational\s+[Cc]ompetent\s+[Aa]uthority|autorité\s+compétente\s+nationale)', 'authority', 0.9),
        (r'\b([Cc]ompetent\s+[Aa]uthority|autorité\s+compétente)', 'authority', 0.85),
        (r'\b(ANSM|MHRA|BfArM|AIFA|AEMPS)', 'authority', 0.9),

        # Legal references - French and English
        (r'\b(Article\s+\d+[a-z]?)', 'legal_reference', 0.9),
        (r'\b(Annexe?\s+[IVX]+|Annex\s+[IVX]+)', 'legal_reference', 0.9),
        (r'\b(Appendice?\s+[IVX]+|Appendix\s+[IVX]+)', 'legal_reference', 0.85),
        (r'\b(Règlement\s+du\s+Conseil|Council\s+Regulation)\s+\([A-Z]+\)\s+[Nn]°?\s*\d+/\d+', 'legal_reference', 0.95),
        (r'\b(Règlement|Regulation)\s+\([A-Z]+\)\s+[Nn]°?\s*\d+/\d+', 'legal_reference', 0.9),
        (r'\b(Directive\s+\d+/\d+/[A-Z]+)', 'legal_reference', 0.9),
        (r'\b(ICH/?VICH|ICH\s+[A-Z]\d+)', 'legal_reference', 0.9),
        (r'\b(GCP|GMP|GLP|BPF|BPC|BPL)\b', 'legal_reference', 0.8),
        (r'\b(lignes?\s+directrices?\s+applicables?|guidelines?)', 'legal_reference', 0.8),
        (r'\b(résumé\s+des\s+caractéristiques\s+du\s+produit|summary\s+of\s+product\s+characteristics)',
         'legal_reference', 0.85),

    ]

    # Add special detection for STRUCTURED French conditions and documents
    structured_entities = find_structured_french_entities(text)
    entities.extend(structured_entities)

    for pattern, entity_type, confidence in aggressive_patterns:
        for match in re.finditer(pattern, text, re.IGNORECASE):
            matched_text = match.group(1) if match.groups() else match.group()

            # Clean up the matched text
            matched_text = matched_text.strip()
            if len(matched_text) > 2:  # Only keep meaningful matches
                entities.append({
                    'text': matched_text,
                    'start_pos': match.start(),
                    'end_pos': match.end(),
                    'type': entity_type,
                    'confidence': confidence,
                    'reasoning': f'Aggressive pattern match for {entity_type}'
                })

    print(f"🔍 Aggressive patterns found {len(entities)} entities")

    # Debug: show what types were found by patterns
    type_counts = {}
    for ent in entities:
        type_counts[ent['type']] = type_counts.get(ent['type'], 0) + 1
    print(f"📊 Pattern types: {type_counts}")

    return entities


def combine_llm_and_patterns(llm_results: List[Dict], pattern_results: List[Dict], text: str) -> List[Dict]:
    """
    Combine LLM and pattern results with smart filtering for false positives
    """
    combined = []
    seen_positions = set()

    print(f"🔄 Combining {len(llm_results)} LLM results with {len(pattern_results)} pattern results")

    # Prioritize LLM results
    for ann in llm_results:
        pos_key = (ann['start_pos'], ann['end_pos'])
        if pos_key not in seen_positions:
            seen_positions.add(pos_key)
            combined.append(ann)

    # Add pattern results that don't overlap AND pass smart filtering
    for ann in pattern_results:
        pos_key = (ann['start_pos'], ann['end_pos'])
        if pos_key not in seen_positions:
            # Check for text overlap
            overlaps = False
            for existing in combined:
                if (ann['start_pos'] < existing['end_pos'] and
                        ann['end_pos'] > existing['start_pos']):
                    overlaps = True
                    break

            if not overlaps and is_valid_entity(ann):
                seen_positions.add(pos_key)
                combined.append(ann)
            elif not overlaps:
                print(f"❌ Filtered false positive: '{ann['text']}' ({ann['type']})")

    print(f"✅ Combined to {len(combined)} unique annotations")
    return combined


def is_valid_entity(ann: Dict) -> bool:
    """
    Smart filter to catch false positives
    """
    entity_type = ann['type']
    text = ann['text'].strip().lower()

    # DELAY: Must be actual time periods, NOT directional words
    if entity_type == 'delay':
        false_delays = ['avant', 'après', 'before', 'after', 'during', 'pendant']
        if text in false_delays:
            return False
        # Must contain numbers or specific time words
        if not re.search(r'\d+|immédiatement|immediately|trentième|dès que', text):
            return False

    # REQUIRED_CONDITION: Must be actual conditions, NOT headers
    elif entity_type == 'required_condition':
        false_conditions = ['conditions', 'conditions à remplir', 'exigences', 'requirements']
        if text in false_conditions:
            return False
        # Must be numbered item or contain obligation words
        if not re.search(r'^\d+\.|doit|must|shall|requise?|nécessaire|obligatoire', text):
            return False

    # REQUIRED_DOCUMENT: Must be actual documents, NOT headers
    elif entity_type == 'required_document':
        false_documents = ['documents', 'documents à fournir', 'documentation']
        if text in false_documents:
            return False
        # Must be numbered item or contain submission words
        if not re.search(r'^\d+\.|version|justification|déclaration|études?|dossier|rapport', text):
            return False

    # AUTHORITY: Must be actual authority names, NOT the word "authority"
    elif entity_type == 'authority':
        false_authorities = ['authority', 'authorities', 'autorité', 'autorités']
        if text in false_authorities:
            return False

    # LEGAL_REFERENCE: Must be actual references, NOT the word "reference"
    elif entity_type == 'legal_reference':
        false_references = ['reference', 'références', 'legal', 'légal']
        if text in false_references:
            return False

    return True


def validate_annotation_positions(text: str, annotations: List[Dict]) -> List[Dict]:
    """
    Validate and fix annotation positions with DEBUG
    """
    validated = []

    print(f"🔍 Validating {len(annotations)} annotation positions...")

    for i, ann in enumerate(annotations):
        start = ann['start_pos']
        end = ann['end_pos']
        expected_text = ann['text']

        if 0 <= start < end <= len(text):
            actual_text = text[start:end]
            if actual_text.strip().lower() == expected_text.strip().lower():
                validated.append(ann)
                print(f"  ✅ {i + 1}: Perfect match '{expected_text[:20]}...'")
            else:
                print(f"  ⚠️  {i + 1}: Position mismatch for '{expected_text[:20]}...'")
                print(f"      Expected: '{expected_text}'")
                print(f"      Got: '{actual_text}'")

                # Try to find the text nearby
                search_text = expected_text.strip()

                # Search in a window around the expected position
                search_start = max(0, start - 100)
                search_end = min(len(text), end + 100)
                search_area = text[search_start:search_end]

                found_pos = search_area.lower().find(search_text.lower())
                if found_pos != -1:
                    global_pos = search_start + found_pos
                    ann['start_pos'] = global_pos
                    ann['end_pos'] = global_pos + len(search_text)
                    validated.append(ann)
                    print(f"      ✅ Fixed position for: '{search_text[:20]}...'")
                else:
                    # Try exact match in full text
                    full_matches = [m.start() for m in re.finditer(re.escape(search_text), text, re.IGNORECASE)]
                    if full_matches:
                        ann['start_pos'] = full_matches[0]
                        ann['end_pos'] = full_matches[0] + len(search_text)
                        validated.append(ann)
                        print(f"      ✅ Found exact match for: '{search_text[:20]}...'")
                    else:
                        print(f"      ❌ Could not validate: '{expected_text[:20]}...'")
        else:
            print(f"  ❌ {i + 1}: Invalid position range for '{expected_text[:20]}...'")

    print(f"📍 Validated {len(validated)} out of {len(annotations)} annotations")

    # Fix overlapping annotations
    validated = fix_overlapping_annotations(validated, text)
    return validated


def get_annotation_colors():
    """
    Return color mapping for different annotation types
    """
    return {
        'procedure_type': '#3b82f6',  # Blue
        'country': '#10b981',  # Green
        'authority': '#8b5cf6',  # Purple
        'legal_reference': '#f59e0b',  # Yellow
        'required_document': '#ef4444',  # Red
        'required_condition': '#06b6d4',  # Cyan
        'delay': '#84cc16',  # Lime
        'variation_code': '#f97316',  # Orange
        'file_type': '#6b7280',  # Gray
    }


def create_annotation_types():
    """
    Create default annotation types in database
    """
    from .models import AnnotationType

    types_data = [
        ('procedure_type', 'Code de Variation', '#3b82f6', 'Types de procédures (IA, IB, II)'),
        ('country', 'Pays', '#10b981', 'Pays et régions géographiques'),
        ('authority', 'Autorité', '#8b5cf6', 'Autorités réglementaires (EMA, FDA)'),
        ('legal_reference', 'Référence Légale', '#f59e0b', 'Références légales et réglementaires'),
        ('required_document', 'Document Requis', '#ef4444', 'Documents requis pour les procédures'),
        ('required_condition', 'Condition Requise', '#06b6d4', 'Conditions et exigences'),
        ('delay', 'Délai', '#84cc16', 'Délais et périodes de temps'),
        ('variation_code', 'Type de Procédure', '#f97316', 'Codes de variation spécifiques'),
        ('file_type', 'Type de Dossier', '#6b7280', 'Types de fichiers et formats'),
    ]

    for name, display_name, color, description in types_data:
        AnnotationType.objects.get_or_create(
            name=name,
            defaults={
                'display_name': display_name,
                'color': color,
                'description': description
            }
        )

    print("✅ Annotation types created/updated")


def fix_overlapping_annotations(annotations, text):
    """
    Fix overlapping annotations
    """
    if not annotations:
        return annotations

    # Sort by start position
    sorted_annotations = sorted(annotations, key=lambda x: x['start_pos'])

    fixed_annotations = []
    for ann in sorted_annotations:
        # Check if positions are valid
        if (0 <= ann['start_pos'] < ann['end_pos'] <= len(text)):
            # Check for overlaps
            overlaps = False
            for existing in fixed_annotations:
                if (ann['start_pos'] < existing['end_pos'] and
                        ann['end_pos'] > existing['start_pos']):
                    overlaps = True
                    break

            if not overlaps:
                fixed_annotations.append(ann)

    return fixed_annotations