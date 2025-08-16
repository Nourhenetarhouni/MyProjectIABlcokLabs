# rawdocs/rlhf_learning.py - NEW FILE
"""
Reinforcement Learning from Human Feedback system for GROQ annotation improvement
"""

import json
import os
import requests
import time
from collections import defaultdict
from datetime import datetime
from typing import List, Dict, Any, Optional


class RLHFGroqAnnotator:
    """
    Enhanced GROQ annotator with Reinforcement Learning from Human Feedback
    """

    def __init__(self):
        # Initialize base GROQ settings
        self.api_url = "https://api.groq.com/openai/v1/chat/completions"
        self.model = "llama-3.3-70b-versatile"
        self.api_key = os.getenv("GROQ_API_KEY")

        if not self.api_key:
            raise ValueError("GROQ_API_KEY environment variable not set")

        # RLHF components
        self.optimized_prompts = {}
        self.performance_metrics = {}

        # Load existing learning data
        self.load_learning_data()

    def load_learning_data(self):
        """Load previous feedback and optimizations"""
        try:
            from .models import PromptOptimization, AILearningMetrics

            # Load prompt optimizations
            optimizations = PromptOptimization.objects.filter(is_active=True)
            for opt in optimizations:
                self.optimized_prompts[opt.entity_type] = opt.optimized_prompt

            # Load performance metrics
            latest_metrics = AILearningMetrics.objects.order_by('-created_at').first()
            if latest_metrics:
                self.performance_metrics = latest_metrics.entity_performance

            print(f"🧠 Loaded {len(self.optimized_prompts)} optimized prompts")

        except Exception as e:
            print(f"⚠️  No previous learning data: {e}")

    def create_adaptive_prompt(self, text: str) -> str:
        """Create prompt that adapts based on previous feedback"""

        # Base prompt structure
        base_context = """You are an expert regulatory document analyst. Learn from previous corrections to improve accuracy."""

        # Add learning context from feedback
        learning_context = ""
        if self.optimized_prompts:
            learning_context = "\n**LEARNED OPTIMIZATIONS:**\n"
            for entity_type, optimization in list(self.optimized_prompts.items())[:3]:
                learning_context += f"- {entity_type}: {optimization}\n"

        # Add common mistakes to avoid
        common_mistakes = self.get_common_mistakes()
        mistake_context = ""
        if common_mistakes:
            mistake_context = f"\n**AVOID THESE COMMON MISTAKES:**\n{common_mistakes}\n"

        # Add positive patterns to reinforce
        positive_patterns = self.get_positive_patterns()
        positive_context = ""
        if positive_patterns:
            positive_context = f"\n**CONTINUE THESE SUCCESSFUL PATTERNS:**\n{positive_patterns}\n"

        return f"""{base_context}
{learning_context}
{mistake_context}
{positive_context}

**ENTITY TYPES TO FIND:**
- **VARIATION_CODE**: Regulatory codes like C.I.6, C.I.7, etc.
- **PROCEDURE_TYPE**: Procedure codes like IA, IB, II, Type IA, etc.
- **AUTHORITY**: Regulatory bodies like EMA, CHMP, ICH, FDA, etc.
- **LEGAL_REFERENCE**: Legal citations, document codes, annexes, articles
- **REQUIRED_CONDITION**: COMPLETE sentences describing requirements
- **REQUIRED_DOCUMENT**: Specific document names (not headers)
- **DELAY**: Time constraints like "within 30 days", "by 31 December"

**CRITICAL RULES:**
1. ONLY extract text that is PHYSICALLY PRESENT in the document
2. DO NOT extract headers, numbers, or generic terms
3. Extract COMPLETE sentences for conditions and documents
4. Apply learned optimizations from previous feedback

**DOCUMENT TEXT:**
```
{text}
```

Return JSON array with exact text positions:
[{{"text": "exact text", "start_pos": 123, "end_pos": 130, "type": "entity_type", "confidence": 0.95, "reasoning": "explanation"}}]"""

    def get_common_mistakes(self) -> str:
        """Get common mistakes from feedback history"""
        try:
            from .models import AnnotationFeedback
            recent_feedbacks = AnnotationFeedback.objects.order_by('-validated_at')[:20]

            mistakes = []
            for feedback in recent_feedbacks:
                corrections = feedback.corrections_made
                if 'false_positives' in corrections:
                    for fp in corrections['false_positives'][:2]:
                        mistakes.append(f"- Don't extract '{fp['text']}' as {fp['type']}")

            return "\n".join(mistakes[:8])

        except Exception:
            return ""

    def get_positive_patterns(self) -> str:
        """Get successful patterns to reinforce"""
        try:
            from .models import AnnotationFeedback
            good_feedbacks = AnnotationFeedback.objects.filter(
                feedback_score__gte=0.8
            ).order_by('-validated_at')[:10]

            patterns = []
            for feedback in good_feedbacks:
                corrections = feedback.corrections_made
                if 'kept_correct' in corrections:
                    for correct in corrections['kept_correct'][:2]:
                        patterns.append(f"- '{correct['text']}' as {correct['type']} ✓")

            return "\n".join(patterns[:6])

        except Exception:
            return ""

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
                    "content": "You are an expert regulatory document analyst. Extract entities with perfect precision."
                },
                {
                    "role": "user",
                    "content": prompt
                }
            ],
            "temperature": 0.1,
            "max_tokens": max_tokens,
            "top_p": 0.9
        }

        try:
            response = requests.post(
                self.api_url,
                headers=headers,
                json=payload,
                timeout=120
            )

            if response.status_code == 200:
                result = response.json()
                return result['choices'][0]['message']['content']
            elif response.status_code == 429:
                print("⚠️  Rate limit reached, waiting...")
                time.sleep(60)
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
                        item['page_num'] = page_num
                        item['source'] = 'rlhf_groq_llama3.3_70b'

                        if 'confidence' not in item:
                            item['confidence'] = 0.8
                        else:
                            item['confidence'] = float(item['confidence'])

                        if 'start_pos' not in item:
                            item['start_pos'] = 0
                        if 'end_pos' not in item:
                            item['end_pos'] = len(item['text'])

                        annotations.append(item)

                print(f"✅ Parsed {len(annotations)} annotations from RLHF GROQ")
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
            import re
            json_match = re.search(r'```json\s*(\[.*?\])\s*```', response, re.DOTALL)
            if json_match:
                return json.loads(json_match.group(1))
        except:
            pass

        # Look for JSON array
        try:
            import re
            json_match = re.search(r'(\[.*?\])', response, re.DOTALL)
            if json_match:
                return json.loads(json_match.group(1))
        except:
            pass

        return None

    def process_human_feedback(self, page_id: int, ai_annotations: list, human_annotations: list, annotator_id: int):
        """Process human feedback and learn from it"""

        print(f"🎓 Processing feedback for page {page_id}...")

        # Analyze corrections
        corrections = self.analyze_corrections(ai_annotations, human_annotations)

        # Calculate feedback score
        feedback_score = self.calculate_feedback_score(corrections)

        # Save feedback to database
        self.save_feedback(page_id, ai_annotations, human_annotations, corrections, feedback_score, annotator_id)

        # Update learning algorithms
        self.update_learning_models(corrections)

        # Optimize prompts based on feedback
        self.optimize_prompts_from_feedback(corrections)

        return {
            'feedback_score': feedback_score,
            'corrections_summary': corrections,
            'learning_updated': True
        }

    def analyze_corrections(self, ai_annotations: list, human_annotations: list) -> dict:
        """Analyze what the human corrected"""

        corrections = {
            'false_positives': [],  # AI found but human removed
            'false_negatives': [],  # AI missed but human added
            'wrong_classifications': [],  # AI found but wrong type
            'kept_correct': [],  # AI found and human kept
        }

        # Convert to comparable format
        ai_items = {f"{ann['text']}_{ann['type']}": ann for ann in ai_annotations}
        human_items = {f"{ann['text']}_{ann['type']}": ann for ann in human_annotations}

        # Find false positives and wrong classifications
        for ai_key, ai_ann in ai_items.items():
            if ai_key not in human_items:
                # Check if same text exists with different type
                same_text_diff_type = None
                for h_key, h_ann in human_items.items():
                    if h_ann['text'] == ai_ann['text'] and h_ann['type'] != ai_ann['type']:
                        same_text_diff_type = h_ann
                        break

                if same_text_diff_type:
                    corrections['wrong_classifications'].append({
                        'text': ai_ann['text'],
                        'wrong_type': ai_ann['type'],
                        'correct_type': same_text_diff_type['type']
                    })
                else:
                    corrections['false_positives'].append(ai_ann)

        # Find false negatives
        for human_key, human_ann in human_items.items():
            if human_key not in ai_items:
                corrections['false_negatives'].append(human_ann)

        # Find kept correct
        for ai_key, ai_ann in ai_items.items():
            if ai_key in human_items:
                corrections['kept_correct'].append(ai_ann)

        return corrections

    def calculate_feedback_score(self, corrections: dict) -> float:
        """
        Calculate comprehensive feedback score (0-1) including missed annotations

        Formula: Correct AI annotations ÷ Total expected annotations

        Where:
        - Correct AI annotations = annotations the human kept
        - Total expected annotations = AI correct + AI wrong + Human additions
        """

        ai_correct = len(corrections['kept_correct'])  # ✅ AI got right
        ai_wrong = len(corrections['false_positives'])  # ❌ AI wrong (deleted)
        ai_misclassified = len(corrections['wrong_classifications'])  # 🔄 AI wrong type
        human_additions = len(corrections['false_negatives'])  # ➕ AI missed (added)

        # Total annotations that should have been found
        total_expected = ai_correct + ai_wrong + ai_misclassified + human_additions

        if total_expected == 0:
            return 1.0  # Perfect if no annotations needed

        # Only count perfectly correct AI annotations
        perfectly_correct = ai_correct

        feedback_score = perfectly_correct / total_expected

        # Debug logging
        print(f"""
        🎓 Feedback Calculation:
        ✅ AI Correct (kept): {ai_correct}
        ❌ AI Wrong (deleted): {ai_wrong} 
        🔄 AI Wrong Type: {ai_misclassified}
        ➕ AI Missed (added): {human_additions}
        📊 Total Expected: {total_expected}
        🎯 Score: {feedback_score:.2%}
        """)

        return feedback_score

    def save_feedback(self, page_id: int, ai_annotations: list, human_annotations: list,
                      corrections: dict, feedback_score: float, annotator_id: int):
        """Save feedback to database"""

        try:
            from .models import AnnotationFeedback, DocumentPage
            from django.contrib.auth.models import User

            page = DocumentPage.objects.get(id=page_id)
            annotator = User.objects.get(id=annotator_id)

            AnnotationFeedback.objects.update_or_create(
                page=page,
                annotator=annotator,
                defaults={
                    'ai_annotations_before': ai_annotations,
                    'human_annotations_after': human_annotations,
                    'corrections_made': corrections,
                    'feedback_score': feedback_score
                }
            )

            print(f"✅ Feedback saved with score: {feedback_score:.2f}")

        except Exception as e:
            print(f"❌ Error saving feedback: {e}")

    def update_learning_models(self, corrections: dict):
        """Update AI performance metrics"""

        try:
            from .models import AILearningMetrics

            # Calculate metrics
            total_correct = len(corrections['kept_correct'])
            total_fp = len(corrections['false_positives'])
            total_fn = len(corrections['false_negatives'])

            precision = total_correct / (total_correct + total_fp) if (total_correct + total_fp) > 0 else 0
            recall = total_correct / (total_correct + total_fn) if (total_correct + total_fn) > 0 else 0
            f1 = 2 * (precision * recall) / (precision + recall) if (precision + recall) > 0 else 0

            # Save metrics
            AILearningMetrics.objects.create(
                precision_score=precision,
                recall_score=recall,
                f1_score=f1,
                total_feedbacks=1,
                entity_performance=self.calculate_entity_performance(corrections)
            )

            print(f"📊 Metrics updated: P={precision:.2f}, R={recall:.2f}, F1={f1:.2f}")

        except Exception as e:
            print(f"❌ Error updating metrics: {e}")

    def calculate_entity_performance(self, corrections: dict) -> dict:
        """Calculate performance per entity type"""

        entity_performance = defaultdict(lambda: {'correct': 0, 'fp': 0, 'fn': 0})

        for item in corrections['kept_correct']:
            entity_performance[item['type']]['correct'] += 1

        for item in corrections['false_positives']:
            entity_performance[item['type']]['fp'] += 1

        for item in corrections['false_negatives']:
            entity_performance[item['type']]['fn'] += 1

        return dict(entity_performance)

    def optimize_prompts_from_feedback(self, corrections: dict):
        """Optimize prompts based on feedback patterns"""

        try:
            from .models import PromptOptimization

            # Analyze patterns for each entity type
            entity_feedback = defaultdict(list)

            for fp in corrections['false_positives']:
                entity_feedback[fp['type']].append(f"Don't extract '{fp['text']}'")

            for wc in corrections['wrong_classifications']:
                entity_feedback[wc['wrong_type']].append(
                    f"'{wc['text']}' is {wc['correct_type']}, not {wc['wrong_type']}")

            # Update prompts
            for entity_type, feedback_list in entity_feedback.items():
                if len(feedback_list) >= 2:  # Only optimize if enough feedback

                    optimization_text = f"""Based on recent feedback:
{chr(10).join(feedback_list[:3])}
Focus on precision for {entity_type}."""

                    PromptOptimization.objects.update_or_create(
                        entity_type=entity_type,
                        defaults={
                            'optimized_prompt': optimization_text,
                            'performance_score': 0.0,
                            'feedback_count': len(feedback_list)
                        }
                    )

                    print(f"🎯 Optimized prompt for {entity_type}")

        except Exception as e:
            print(f"❌ Error optimizing prompts: {e}")