from django.db import models
from django.utils import timezone
from client.products.models import Product
from datetime import datetime, timedelta
import json

class ReportSubmission(models.Model):
    """Model pour les soumissions réglementaires"""
    STATUS_CHOICES = [
        ('en-cours', 'En cours'),
        ('approuve', 'Approuvé'),
        ('rejete', 'Rejeté'),
        ('en-attente', 'En attente'),
    ]
    
    TYPE_CHOICES = [
        ('autorisation', 'Autorisation initiale'),
        ('variation_ia', 'Variation Type IA'),
        ('variation_ib', 'Variation Type IB'),
        ('variation_ii', 'Variation Type II'),
        ('renouvellement', 'Renouvellement'),
    ]
    
    product = models.ForeignKey(Product, on_delete=models.CASCADE, related_name='submissions')
    type = models.CharField(max_length=20, choices=TYPE_CHOICES, verbose_name="Type de soumission")
    status = models.CharField(max_length=20, choices=STATUS_CHOICES, default='en-cours')
    submission_date = models.DateField(verbose_name="Date de soumission")
    estimated_completion = models.DateField(verbose_name="Date d'achèvement estimée")
    actual_completion = models.DateField(null=True, blank=True, verbose_name="Date d'achèvement réelle")
    responsible = models.CharField(max_length=100, verbose_name="Responsable")
    progress = models.IntegerField(default=0, verbose_name="Progression (%)")
    
    # Métadonnées
    team = models.CharField(max_length=50, blank=True, verbose_name="Équipe")
    priority = models.CharField(max_length=20, default='normale', verbose_name="Priorité")
    notes = models.TextField(blank=True, verbose_name="Notes")
    
    created_at = models.DateTimeField(auto_now_add=True)
    updated_at = models.DateTimeField(auto_now=True)
    
    class Meta:
        verbose_name = "Soumission réglementaire"
        verbose_name_plural = "Soumissions réglementaires"
        ordering = ['-submission_date']
    
    def __str__(self):
        return f"{self.product.name} - {self.get_type_display()}"
    
    @property
    def days_delay(self):
        """Calcule le retard en jours"""
        target_date = self.actual_completion or self.estimated_completion
        today = timezone.now().date()
        return (today - target_date).days
    
    @property
    def is_delayed(self):
        """Vérifie si la soumission est en retard"""
        return self.days_delay > 0 and self.status != 'approuve'
    
    def get_status_color(self):
        """Retourne la couleur du statut"""
        colors = {
            'en-cours': '#3498db',
            'approuve': '#27ae60',
            'rejete': '#e74c3c',
            'en-attente': '#f39c12'
        }
        return colors.get(self.status, '#6c757d')

class ReportKPI(models.Model):
    """Model pour stocker les KPIs calculés"""
    date = models.DateField(default=timezone.now)
    period = models.CharField(max_length=10, default='30d')
    
    # KPIs principaux
    total_submissions = models.IntegerField(default=0)
    average_delay = models.FloatField(default=0.0)
    success_rate = models.FloatField(default=0.0)
    delayed_count = models.IntegerField(default=0)
    
    # Tendances (pourcentages)
    submissions_trend = models.FloatField(default=0.0)
    delay_trend = models.FloatField(default=0.0)
    success_trend = models.FloatField(default=0.0)
    delayed_trend = models.FloatField(default=0.0)
    
    # Données des graphiques (JSON)
    trend_data = models.JSONField(default=dict)
    status_data = models.JSONField(default=dict)
    
    class Meta:
        verbose_name = "KPI Report"
        verbose_name_plural = "KPIs Reports"
        unique_together = ['date', 'period']
    
    def __str__(self):
        return f"KPI {self.date} - {self.period}"

class ReportHeatmap(models.Model):
    """Model pour les données de heatmap"""
    product = models.ForeignKey(Product, on_delete=models.CASCADE)
    date = models.DateField(default=timezone.now)
    
    # Délais par type
    authorization_delay = models.IntegerField(null=True, blank=True)
    variation_delay = models.IntegerField(null=True, blank=True)
    renewal_delay = models.IntegerField(null=True, blank=True)
    
    # Statuts (good, warning, critical)
    authorization_status = models.CharField(max_length=10, default='good')
    variation_status = models.CharField(max_length=10, default='good')
    renewal_status = models.CharField(max_length=10, default='good')
    
    class Meta:
        verbose_name = "Heatmap Data"
        verbose_name_plural = "Heatmap Data"
        unique_together = ['product', 'date']
    
    def __str__(self):
        return f"Heatmap {self.product.name} - {self.date}"