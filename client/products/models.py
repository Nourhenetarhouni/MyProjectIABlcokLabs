from django.db import models
from django.urls import reverse

class Product(models.Model):
    STATUS_CHOICES = [
        ('commercialise', 'Commercialisé'),
        ('developpement', 'En développement'),
        ('arrete', 'Arrêté'),
    ]
    
    name = models.CharField(max_length=255, verbose_name="Nom du produit")
    active_ingredient = models.CharField(max_length=255, verbose_name="Principe actif")
    dosage = models.CharField(max_length=100, verbose_name="Dosage")
    form = models.CharField(max_length=100, verbose_name="Forme")
    therapeutic_area = models.CharField(max_length=200, verbose_name="Zone thérapeutique")
    status = models.CharField(max_length=20, choices=STATUS_CHOICES, default='developpement')
    source_document = models.ForeignKey(
        'rawdocs.RawDocument', 
        on_delete=models.SET_NULL, 
        null=True, 
        blank=True,
        verbose_name="Document source",
        help_text="Document original ayant généré ce produit"
    )
    created_at = models.DateTimeField(auto_now_add=True)
    updated_at = models.DateTimeField(auto_now=True)
    
    class Meta:
        verbose_name = "Produit"
        verbose_name_plural = "Produits"
        ordering = ['-created_at']
    
    def __str__(self):
        return self.name
    
    def get_absolute_url(self):
        return reverse('products:detail', kwargs={'pk': self.pk})

class ProductSpecification(models.Model):
    product = models.ForeignKey(Product, on_delete=models.CASCADE, related_name='specifications')
    country_code = models.CharField(max_length=3, verbose_name="Code pays")
    amm_number = models.CharField(max_length=100, verbose_name="Numéro AMM")
    approval_date = models.DateField(verbose_name="Date d'approbation")
    renewal_date = models.DateField(verbose_name="Date de renouvellement")
    
    # Documents status
    ctd_dossier_complete = models.BooleanField(default=False, verbose_name="Dossier CTD complet")
    gmp_certificate = models.BooleanField(default=False, verbose_name="Certificat GMP")
    inspection_report = models.BooleanField(default=False, verbose_name="Rapport d'inspection")
    rcp_etiquetage = models.BooleanField(default=False, verbose_name="RCP et étiquetage")
    
    is_active = models.BooleanField(default=True, verbose_name="Actif")
    
    class Meta:
        verbose_name = "Spécification produit"
        verbose_name_plural = "Spécifications produits"
        unique_together = ['product', 'country_code']
    
    def __str__(self):
        return f"{self.product.name} - {self.country_code}"

class ManufacturingSite(models.Model):
    product = models.ForeignKey(Product, on_delete=models.CASCADE, related_name='sites')
    country = models.CharField(max_length=100, verbose_name="Pays")
    city = models.CharField(max_length=100, verbose_name="Ville")
    site_name = models.CharField(max_length=255, verbose_name="Nom du site")
    
    gmp_certified = models.BooleanField(default=False, verbose_name="Certifié GMP")
    gmp_expiry = models.DateField(null=True, blank=True, verbose_name="Expiration GMP")
    last_audit = models.DateField(null=True, blank=True, verbose_name="Dernier audit")
    
    class Meta:
        verbose_name = "Site de fabrication"
        verbose_name_plural = "Sites de fabrication"
    
    def __str__(self):
        return f"{self.site_name} - {self.city}"

class ProductVariation(models.Model):
    VARIATION_TYPES = [
        ('type_ia', 'Type IA'),
        ('type_ib', 'Type IB'),
        ('type_ii', 'Type II'),
    ]
    
    STATUS_CHOICES = [
        ('soumis', 'Soumis'),
        ('en_cours', 'En cours'),
        ('approuve', 'Approuvé'),
        ('rejete', 'Rejeté'),
    ]
    
    product = models.ForeignKey(Product, on_delete=models.CASCADE, related_name='variations')
    variation_type = models.CharField(max_length=10, choices=VARIATION_TYPES)
    title = models.CharField(max_length=255, verbose_name="Titre")
    description = models.TextField(verbose_name="Description")
    submission_date = models.DateField(verbose_name="Date de soumission")
    approval_date = models.DateField(null=True, blank=True, verbose_name="Date d'approbation")
    status = models.CharField(max_length=20, choices=STATUS_CHOICES, default='soumis')
    
    class Meta:
        verbose_name = "Variation produit"
        verbose_name_plural = "Variations produits"
        ordering = ['-submission_date']
    
    def __str__(self):
        return f"{self.title} - {self.variation_type}"