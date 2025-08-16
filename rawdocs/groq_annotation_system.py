# groq_annotation_system.py
from django.shortcuts import render, get_object_or_404
from django.http import JsonResponse
from django.contrib.auth.decorators import login_required
from django.views.decorators.csrf import csrf_exempt
from django.contrib import messages
from datetime import datetime

import requests
import json
import time
from typing import List, Dict, Any, Optional
import re
import os


class GroqAnnotator:
    """
    FREE GROQ API + Llama 3.1 70B implementation for regulatory document annotation
    ZERO COST - Claude-level professional results!
    """

    def __init__(self):
        # GROQ settings - FREE 6000 requests/day
        self.api_url = "https://api.groq.com/openai/v1/chat/completions"
        self.model = "llama-3.3-70b-versatile"  # BEST FREE model!
        self.api_key = os.getenv("GROQ_API_KEY")

        if not self.api_key:
            raise ValueError("GROQ_API_KEY environment variable not set. Get free key from https://console.groq.com/")

        print("🚀 Using GROQ FREE API (Llama 3.3 70B - BEST!)")
        self.test_connection()

    def test_connection(self) -> bool:
        """Test GROQ API connection"""
        try:
            test_response = self.call_groq_api("Test connection", max_tokens=10)
            if test_response:
                print("✅ GROQ API connected successfully!")
                return True
            else:
                print("❌ GROQ API connection failed")
                return False
        except Exception as e:
            print(f"❌ GROQ connection error: {e}")
            return False

    def annotate_page_with_groq(self, page_data: Dict[str, Any]) -> List[Dict[str, Any]]:
        """Use GROQ Llama 3.1 70B for annotation - Claude-level quality"""

        text = page_data['text']
        page_num = page_data['page_num']

        if len(text.strip()) < 50:  # Skip empty pages
            return []

        print(f"🧠 Processing page {page_num} with GROQ Llama 3.3 70B...")

        # Create Claude-level expert prompt
        prompt = self.create_expert_prompt(text)

        try:
            # Call GROQ API
            response = self.call_groq_api(prompt)

            if response:
                # Parse the response
                annotations = self.parse_groq_response(response, page_num)
                return annotations
            else:
                print(f"❌ No response for page {page_num}")
                return []

        except Exception as e:
            print(f"❌ Error processing page {page_num}: {e}")
            return []

    def create_expert_prompt(self, text: str) -> str:
        """Create EXPERT-LEVEL prompt for Claude-quality results - NO EXAMPLES TO CONFUSE MODEL"""

        return f"""You are an expert regulatory document analyst. Your ONLY job is to find entities that LITERALLY EXIST in the document text below.

**CRITICAL RULES:**
1. ONLY extract text that is PHYSICALLY PRESENT in the document below
2. DO NOT use any examples from this prompt
3. DO NOT extract "Documents", "Conditions", "1.", "2.", "3." or other headers
4. DO NOT make up or imagine anything
5. Extract COMPLETE sentences for conditions and documents

**ENTITY TYPES TO FIND:**

**VARIATION_CODE**: Regulatory codes like C.I.6, C.I.7, etc.
**PROCEDURE_TYPE**: Procedure codes like IA, IB, II, Type IA, etc.
**AUTHORITY**: Regulatory bodies like EMA, CHMP, ICH, FDA, etc.
**LEGAL_REFERENCE**: Legal citations, document codes, annexes, articles
**REQUIRED_CONDITION**: COMPLETE sentences describing requirements
**REQUIRED_DOCUMENT**: Specific document names (not headers)
**DELAY**: exemple : "within 30 days", "by 31 December", "dans 15 jours", ect..

**VALIDATION CHECKLIST:**
- Is this text EXACTLY in the document below? ✓
- Is this a header like "Documents" or "Conditions"? ✗ SKIP
- Is this a number like "1." or "2."? ✗ SKIP  
- Is this from the prompt examples? ✗ SKIP
- Is this a complete sentence for conditions/documents? ✓

**DOCUMENT TEXT:**
```
{text}
```

**TASK:** Find ONLY entities that are LITERALLY in the document above.

Return JSON array:
[{{"text": "exact text from document", "start_pos": 123, "end_pos": 130, "type": "variation_code|procedure_type|authority|legal_reference|required_condition|required_document|delay", "confidence": 0.95, "reasoning": "found this exact text in document"}}]

**NO EXAMPLES - ONLY REAL TEXT FROM DOCUMENT ABOVE**"""

    def call_groq_api(self, prompt: str, max_tokens: int = 4000) -> Optional[str]:
        """Call GROQ API with optimized settings"""

        headers = {
            "Authorization": f"Bearer {self.api_key}",
            "Content-Type": "application/json"
        }

        payload = {
            "model": self.model,
            "messages": [
                {
                    "role": "system",
                    "content": "You are an expert regulatory document analyst. Extract entities with perfect precision, never hallucinate."
                },
                {
                    "role": "user",
                    "content": prompt
                }
            ],
            "temperature": 0.1,  # Low for consistency
            "max_tokens": max_tokens,
            "top_p": 0.9
        }

        try:
            response = requests.post(
                self.api_url,
                headers=headers,
                json=payload,
                timeout=120  # 2 minutes timeout
            )

            if response.status_code == 200:
                result = response.json()
                return result['choices'][0]['message']['content']
            elif response.status_code == 429:
                print("⚠️  Rate limit reached, waiting...")
                time.sleep(60)  # Wait 1 minute
                return self.call_groq_api(prompt, max_tokens)
            else:
                print(f"❌ GROQ API error {response.status_code}: {response.text}")
                return None

        except requests.RequestException as e:
            print(f"❌ Request error: {e}")
            return None

    def parse_groq_response(self, response: str, page_num: int) -> List[Dict[str, Any]]:
        """Parse GROQ response to extract annotations"""

        try:
            # Extract JSON from response
            json_match = self.extract_json_from_response(response)

            if json_match and isinstance(json_match, list):
                annotations = []

                for item in json_match:
                    if isinstance(item, dict) and all(k in item for k in ['text', 'type']):
                        # Clean up the annotation
                        item['page_num'] = page_num
                        item['source'] = 'groq_llama3.3_70b'

                        # Ensure confidence
                        if 'confidence' not in item:
                            item['confidence'] = 0.8
                        else:
                            item['confidence'] = float(item['confidence'])

                        # Ensure positions
                        if 'start_pos' not in item:
                            item['start_pos'] = 0
                        if 'end_pos' not in item:
                            item['end_pos'] = len(item['text'])

                        annotations.append(item)

                print(f"✅ Parsed {len(annotations)} annotations from GROQ")
                return annotations
            else:
                print("❌ Invalid JSON format in GROQ response")
                return []

        except Exception as e:
            print(f"❌ Parse error: {e}")
            return []

    def extract_json_from_response(self, response: str) -> Optional[Any]:
        """Extract JSON from GROQ response"""

        # Try direct JSON parse
        try:
            return json.loads(response.strip())
        except:
            pass

        # Look for JSON in code blocks
        try:
            json_match = re.search(r'```json\s*(\[.*?\])\s*```', response, re.DOTALL)
            if json_match:
                return json.loads(json_match.group(1))
        except:
            pass

        # Look for JSON array
        try:
            json_match = re.search(r'(\[.*?\])', response, re.DOTALL)
            if json_match:
                return json.loads(json_match.group(1))
        except:
            pass

        return None

    def generate_summary(self, pdf_data: Dict[str, Any], annotations: List[Dict[str, Any]]) -> Dict[str, Any]:
        """Generate processing summary"""

        # Analyze annotations
        type_counts = {}
        confidence_scores = []

        for ann in annotations:
            ann_type = ann.get('type', 'unknown')
            type_counts[ann_type] = type_counts.get(ann_type, 0) + 1
            confidence_scores.append(ann.get('confidence', 0.5))

        avg_confidence = sum(confidence_scores) / len(confidence_scores) if confidence_scores else 0
        high_confidence_count = len([c for c in confidence_scores if c > 0.8])

        return {
            'total_pages': pdf_data.get('total_pages', 0),
            'total_annotations': len(annotations),
            'annotation_breakdown': type_counts,
            'average_confidence': round(avg_confidence, 3),
            'high_confidence_annotations': high_confidence_count,
            'processing_model': self.model,
            'cost': 0.0,  # FREE!
            'quality_grade': 'A' if avg_confidence > 0.85 else 'B+' if avg_confidence > 0.75 else 'B'
        }


@login_required
@csrf_exempt
def ai_annotate_page_groq(request, page_id):
    """Django view for FREE GROQ annotation - Claude-level quality"""

    if request.method != 'POST':
        return JsonResponse({'error': 'POST required'}, status=405)

    try:
        page = get_object_or_404(DocumentPage, id=page_id)

        # Initialize GROQ annotator
        try:
            annotator = GroqAnnotator()
        except ValueError as e:
            return JsonResponse({
                'error': 'GROQ API key not set. Get free key from https://console.groq.com/',
                'details': str(e)
            }, status=500)

        print(f"🚀 Processing page {page.page_number} with FREE GROQ...")

        # Create page data
        page_data = {
            'page_num': page.page_number,
            'text': page.cleaned_text,
            'char_count': len(page.cleaned_text)
        }

        # Process with GROQ
        annotations = annotator.annotate_page_with_groq(page_data)

        # Save to database
        saved_count = 0
        for ann_data in annotations:
            try:
                # Get annotation type
                ann_type, created = AnnotationType.objects.get_or_create(
                    name=ann_data['type'],
                    defaults={
                        'display_name': ann_data['type'].replace('_', ' ').title(),
                        'color': '#3b82f6',  # Blue for GROQ
                        'description': f"GROQ Llama 3.3 70B detected {ann_data['type']}"
                    }
                )

                # Create annotation
                annotation = Annotation.objects.create(
                    page=page,
                    annotation_type=ann_type,
                    start_pos=ann_data.get('start_pos', 0),
                    end_pos=ann_data.get('end_pos', 0),
                    selected_text=ann_data.get('text', ''),
                    confidence_score=ann_data.get('confidence', 0.8) * 100,
                    ai_reasoning=ann_data.get('reasoning', 'GROQ Llama 3.3 70B FREE classification'),
                    created_by=request.user
                )
                saved_count += 1

            except Exception as e:
                print(f"❌ Error saving annotation: {e}")
                continue

        # Update page status
        if saved_count > 0:
            page.is_annotated = True
            page.annotated_at = datetime.now()
            page.annotated_by = request.user
            page.save()

        return JsonResponse({
            'success': True,
            'annotations_created': saved_count,
            'message': f'{saved_count} annotations créées avec GROQ FREE!',
            'cost_estimate': 0.0  # FREE!
        })

    except Exception as e:
        print(f"❌ GROQ annotation error: {e}")
        return JsonResponse({
            'error': f'Erreur GROQ: {str(e)}'
        }, status=500)


if __name__ == "__main__":
    setup_groq()