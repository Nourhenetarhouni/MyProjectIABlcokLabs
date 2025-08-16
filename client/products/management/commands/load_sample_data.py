from django.core.management.base import BaseCommand
from products.models import Product, ProductSpecification, ManufacturingSite, ProductVariation
from datetime import date, datetime

class Command(BaseCommand):
    help = 'Load sample data for products'

    def handle(self, *args, **options):
        # Créer RegXpirin 500mg
        regxpirin, created = Product.objects.get_or_create(
            name="RegXpirin 500mg",
            defaults={
                'active_ingredient': 'Analgésique',
                'dosage': '500mg',
                'form': 'Comprimé',
                'therapeutic_area': 'Cardiovascular',
                'status': 'commercialise'
            }
        )

        # Spécifications par pays
        ProductSpecification.objects.get_or_create(
            product=regxpirin,
            country_code='FR',
            defaults={
                'amm_number': 'EU/1/23/1234/001',
                'approval_date': date(2023, 6, 15),
                'renewal_date': date(2028, 6, 15),
                'ctd_dossier_complete': True,
                'gmp_certificate': True,
                'inspection_report': True,
                'rcp_etiquetage': True,
            }
        )

        # Sites de production
        ManufacturingSite.objects.get_or_create(
            product=regxpirin,
            country='France',
            defaults={
                'city': 'Lyon',
                'site_name': 'Site de Production Lyon',
                'gmp_certified': True,
                'gmp_expiry': date(2025, 12, 31),
                'last_audit': date(2023, 3, 15),
            }
        )

        ManufacturingSite.objects.get_or_create(
            product=regxpirin,
            country='Germany',
            defaults={
                'city': 'Berlin',
                'site_name': 'Berlin Manufacturing Facility',
                'gmp_certified': True,
                'gmp_expiry': date(2025, 8, 20),
                'last_audit': date(2023, 1, 10),
            }
        )

        # Variations
        ProductVariation.objects.get_or_create(
            product=regxpirin,
            title='Nouveau site de fabrication',
            defaults={
                'variation_type': 'type_ib',
                'description': 'Ajout du site de production de Madrid pour la fabrication du produit fini.',
                'submission_date': date(2023, 1, 15),
                'approval_date': date(2023, 4, 20),
                'status': 'approuve'
            }
        )

        ProductVariation.objects.get_or_create(
            product=regxpirin,
            title='Modification formulation',
            defaults={
                'variation_type': 'type_ii',
                'description': 'Modification de la formulation pour améliorer la stabilité du produit.',
                'submission_date': date(2023, 11, 10),
                'status': 'en_cours'
            }
        )

        # Créer RegXcillin 250mg
        regxcillin, created = Product.objects.get_or_create(
            name="RegXcillin 250mg",
            defaults={
                'active_ingredient': 'Antibactérial',
                'dosage': '250mg',
                'form': 'Gélule',
                'therapeutic_area': 'Anti-infectieux',
                'status': 'developpement'
            }
        )

        self.stdout.write(
            self.style.SUCCESS('Sample data loaded successfully!')
        )