from django import forms
from django.forms import ModelForm, TextInput, Select, Textarea, CheckboxInput
from .models import Submission, FormattedTemplate, ModuleSection


class SubmissionForm(ModelForm):
    class Meta:
        model = Submission
        fields = ['name', 'region', 'variation_type', 'change_description']
        widgets = {
            'name': TextInput(attrs={
                'class': 'form-control',
                'placeholder': 'Nom de la soumission (ex: EUA)',
            }),
            'region': Select(attrs={
                'class': 'form-control',
            }),
            'variation_type': Select(attrs={
                'class': 'form-control',
            }),
            'change_description': Select(attrs={
                'class': 'form-control',
            }),
        }

    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)

        # Choix pour change_description basés sur le type de variation
        self.fields['change_description'] = forms.ChoiceField(
            choices=[
                ('ajout_site_fabrication', 'Ajout de site de fabrication primaire'),
                ('changement_specs', 'Changement des spécifications'),
                ('modification_etiquetage', 'Modification de l\'étiquetage'),
                ('extension_indication', 'Extension d\'indication'),
                ('nouveau_dosage', 'Nouveau dosage'),
            ],
            widget=Select(attrs={'class': 'form-control'})
        )


class FormattedTemplateForm(ModelForm):
    class Meta:
        model = FormattedTemplate
        fields = [
            'applicant_name', 'customer_account_number', 'customer_reference',
            'inn_code', 'product_name', 'nationally_authorised',
            'product_procedure_number', 'national_marketing_auth_no',
            'new_procedure', 'response_supplementary', 'unit_type',
            'mode_single', 'mode_grouping', 'procedure_type',
            'description_submission', 'related_products', 'rmp_included',
            'rmp_version', 'related_submission_numbers', 'ectd_sequence',
            'contact_content', 'contact_technical'
        ]

        widgets = {
            'applicant_name': TextInput(attrs={
                'class': 'form-control',
                'placeholder': 'Enter applicant/MAH name'
            }),
            'customer_account_number': TextInput(attrs={
                'class': 'form-control',
                'placeholder': '000000xxxx (only one number for WS and IG)'
            }),
            'customer_reference': TextInput(attrs={
                'class': 'form-control',
                'placeholder': 'Enter reference number'
            }),
            'inn_code': TextInput(attrs={
                'class': 'form-control',
                'placeholder': 'Enter INN/Active substance/ATC Code'
            }),
            'product_name': TextInput(attrs={
                'class': 'form-control',
                'placeholder': 'Enter product name'
            }),
            'nationally_authorised': CheckboxInput(attrs={
                'class': 'form-check-input'
            }),
            'product_procedure_number': TextInput(attrs={
                'class': 'form-control',
                'placeholder': 'EMEA/H/C/XXXX / type / PSUSA/XXXXX/YYYYMM'
            }),
            'national_marketing_auth_no': CheckboxInput(attrs={
                'class': 'form-check-input'
            }),
            'new_procedure': CheckboxInput(attrs={
                'class': 'form-check-input'
            }),
            'response_supplementary': CheckboxInput(attrs={
                'class': 'form-check-input'
            }),
            'unit_type': Select(attrs={
                'class': 'form-control'
            }),
            'mode_single': CheckboxInput(attrs={
                'class': 'form-check-input'
            }),
            'mode_grouping': CheckboxInput(attrs={
                'class': 'form-check-input'
            }),
            'procedure_type': TextInput(attrs={
                'class': 'form-control',
                'value': 'MAA - Marketing Authorisation Application',
                'readonly': True
            }),
            'description_submission': Select(attrs={
                'class': 'form-control'
            }),
            'related_products': Textarea(attrs={
                'class': 'form-control',
                'rows': 3,
                'placeholder': 'Enter product details'
            }),
            'rmp_included': CheckboxInput(attrs={
                'class': 'form-check-input'
            }),
            'rmp_version': TextInput(attrs={
                'class': 'form-control',
                'placeholder': 'RMP version N.'
            }),
            'related_submission_numbers': TextInput(attrs={
                'class': 'form-control',
                'placeholder': 'Enter version and submission number'
            }),
            'ectd_sequence': TextInput(attrs={
                'class': 'form-control',
                'placeholder': 'Enter eCTD sequence number'
            }),
            'contact_content': Textarea(attrs={
                'class': 'form-control',
                'rows': 4,
                'placeholder': 'Enter contact details'
            }),
            'contact_technical': Textarea(attrs={
                'class': 'form-control',
                'rows': 4,
                'placeholder': 'Enter contact details'
            }),
        }

    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)

        # Choix pour unit_type
        self.fields['unit_type'] = forms.ChoiceField(
            choices=[
                ('', 'Please select'),
                ('tablet', 'Tablet'),
                ('capsule', 'Capsule'),
                ('injection', 'Injection'),
                ('oral_solution', 'Oral solution'),
                ('topical_cream', 'Topical cream'),
                ('inhaler', 'Inhaler'),
            ],
            required=False,
            widget=Select(attrs={'class': 'form-control'})
        )

        # Choix pour description_submission
        self.fields['description_submission'] = forms.ChoiceField(
            choices=[
                ('', 'Please select'),
                ('initial_maa', 'Initial Marketing Authorization Application'),
                ('variation_type_ia', 'Type IA variation'),
                ('variation_type_ib', 'Type IB variation'),
                ('variation_type_ii', 'Type II variation'),
                ('annual_reassessment', 'Annual reassessment'),
                ('psur_submission', 'PSUR submission'),
            ],
            required=False,
            widget=Select(attrs={'class': 'form-control'})
        )


class ModuleSectionForm(ModelForm):
    class Meta:
        model = ModuleSection
        fields = ['title', 'description', 'template_content']
        widgets = {
            'title': TextInput(attrs={
                'class': 'form-control',
            }),
            'description': Textarea(attrs={
                'class': 'form-control',
                'rows': 3,
            }),
            'template_content': Textarea(attrs={
                'class': 'form-control',
                'rows': 10,
            }),
        }