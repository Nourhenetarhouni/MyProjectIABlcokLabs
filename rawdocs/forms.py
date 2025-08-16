# rawdocs/forms.py

from django import forms
from django.contrib.auth.forms import UserCreationForm
from django.contrib.auth.models import User, Group

ROLE_CHOICES = [
    ("Metadonneur", "Métadonneur"),
    ("Annotateur",  "Annotateur"),
    ("Expert",      "Expert"),
]

class URLForm(forms.Form):
    pdf_url = forms.URLField(
        label="URL du PDF",
        widget=forms.URLInput(attrs={
            "class":       "upload-cell__input",
            "placeholder": "Entrez l’URL du PDF et appuyez sur Entrée…",
            "id":          "id_pdf_url",
        })
    )

class UploadForm(forms.Form):
    """
    Permet de fournir soit une URL, soit un fichier PDF en upload direct.
    """
    pdf_url  = forms.URLField(
        required=False,
        label="URL du PDF",
        widget=forms.URLInput(attrs={
            "class": "upload-cell__input",
            "placeholder": "Ou collez l’URL du PDF…",
        })
    )
    pdf_file = forms.FileField(
        required=False,
        label="Fichier PDF",
        widget=forms.ClearableFileInput(attrs={
            "class": "upload-cell__input",
        })
    )

    def clean(self):
        cleaned = super().clean()
        url  = cleaned.get('pdf_url')
        file = cleaned.get('pdf_file')
        if not url and not file:
            raise forms.ValidationError(
                "Vous devez fournir soit une URL, soit un fichier PDF."
            )
        return cleaned


class RegisterForm(UserCreationForm):
    email = forms.EmailField(required=True, label="Adresse email")
    role  = forms.ChoiceField(choices=ROLE_CHOICES, label="Profil")

    class Meta:
        model  = User
        fields = ("username", "email", "role", "password1", "password2")

    def save(self, commit=True):
        user = super().save(commit)
        group = Group.objects.get(name=self.cleaned_data["role"])
        user.groups.add(group)
        return user


class MetadataEditForm(forms.Form):
    """
    Formulaire d'édition manuelle des métadonnées.
    """
    title             = forms.CharField(
        label="Titre du document", required=False,
        widget=forms.TextInput(attrs={"placeholder": "Titre…"})
    )
    document_type     = forms.CharField(
        label="Type de document", required=False,
        widget=forms.TextInput(attrs={"placeholder": "guideline, rapport…"})
    )
    document_context  = forms.CharField(
        label="Contexte du document", required=False,
        widget=forms.TextInput(attrs={"placeholder": "Pharmaceutique, légal…"})
    )
    language          = forms.CharField(
        label="Langue", required=False,
        widget=forms.TextInput(attrs={"placeholder": "en, fr, es…"})
    )
    publication_date  = forms.DateField(
        label="Date de publication", required=False,
        widget=forms.DateInput(attrs={'type': 'date'})
    )
    version           = forms.CharField(
        label="Version", required=False,
        widget=forms.TextInput(attrs={"placeholder": "v1.0, 2025-05-06…"})
    )
    source            = forms.CharField(
        label="Source", required=False,
        widget=forms.TextInput(attrs={"placeholder": "EMA, FDA, ANSM…"})
    )
    country           = forms.CharField(
        label="Pays", required=False,
        widget=forms.TextInput(attrs={"placeholder": "EU, FR, US…"})
    )
    url_source        = forms.URLField(
        label="URL source", required=False,
        widget=forms.URLInput(attrs={"placeholder": "https://…"})
    )
