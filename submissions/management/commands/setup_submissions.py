from django.core.management.base import BaseCommand, CommandError
from django.contrib.auth.models import User
from submissions.models import Submission, SubmissionModule, ModuleSection, FormattedTemplate
from submissions.views import generate_ctd_structure


class Command(BaseCommand):
    help = 'Initialise des données de test pour l\'application submissions'

    def add_arguments(self, parser):
        parser.add_argument(
            '--create-user',
            action='store_true',
            help='Crée un utilisateur de test',
        )
        parser.add_argument(
            '--create-samples',
            action='store_true',
            help='Crée des soumissions d\'exemple',
        )
        parser.add_argument(
            '--cleanup',
            action='store_true',
            help='Supprime toutes les données de test',
        )

    def handle(self, *args, **options):
        if options['cleanup']:
            self.cleanup_data()

        if options['create_user']:
            self.create_test_user()

        if options['create_samples']:
            self.create_sample_submissions()

        self.stdout.write(
            self.style.SUCCESS('Configuration terminée avec succès!')
        )

    def cleanup_data(self):
        """Nettoie toutes les données de test"""
        self.stdout.write('Suppression des données existantes...')

        Submission.objects.all().delete()

        self.stdout.write(
            self.style.SUCCESS('Données supprimées avec succès.')
        )

    def create_test_user(self):
        """Crée un utilisateur de test"""
        username = 'testuser'
        email = 'test@example.com'
        password = 'testpass123'

        if User.objects.filter(username=username).exists():
            self.stdout.write(
                self.style.WARNING(f'L\'utilisateur {username} existe déjà.')
            )
            return

        user = User.objects.create_user(
            username=username,
            email=email,
            password=password,
            first_name='Test',
            last_name='User'
        )

        self.stdout.write(
            self.style.SUCCESS(f'Utilisateur créé: {username} / {password}')
        )

    def create_sample_submissions(self):
        """Crée des soumissions d'exemple"""
        # Récupérer un utilisateur ou créer un par défaut
        try:
            user = User.objects.get(username='testuser')
        except User.DoesNotExist:
            user = User.objects.filter(is_superuser=True).first()
            if not user:
                self.stdout.write(
                    self.style.ERROR('Aucun utilisateur trouvé. Créez d\'abord un utilisateur.')
                )
                return

        # Données d'exemple
        sample_submissions = [
            {
                'name': 'EU-MAA-001',
                'region': 'EMA',
                'variation_type': 'MAA',
                'change_description': 'ajout_site_fabrication',
                'status': 'in_progress',
                'progress': 75,
            },
            {
                'name': 'FDA-IND-002',
                'region': 'FDA',
                'variation_type': 'IB',
                'change_description': 'changement_specs',
                'status': 'submitted',
                'progress': 100,
            },
            {
                'name': 'HC-NOC-003',
                'region': 'HC',
                'variation_type': 'IA',
                'change_description': 'modification_etiquetage',
                'status': 'draft',
                'progress': 45,
            },
        ]

        for submission_data in sample_submissions:
            # Créer la soumission
            submission = Submission.objects.create(
                created_by=user,
                **submission_data
            )

            # Générer la structure CTD
            generate_ctd_structure(submission)

            self.stdout.write(
                self.style.SUCCESS(f'Soumission créée: {submission.name}')
            )

        self.stdout.write(
            self.style.SUCCESS('Toutes les soumissions d\'exemple ont été créées.')
        )

    def create_sample_templates(self):
        """Crée des templates d'exemple pour les sections"""
        sections = ModuleSection.objects.filter(section_number='1.1')

        for section in sections:
            template, created = FormattedTemplate.objects.get_or_create(
                section=section,
                defaults={
                    'template_name': f'EMA Template - {section.title}',
                    'applicant_name': 'Exemple Pharmaceutique SA',
                    'customer_account_number': '000000123',
                    'product_name': 'Exemple Product 10mg',
                    'inn_code': 'Examplecin',
                }
            )

            if created:
                self.stdout.write(
                    self.style.SUCCESS(f'Template créé pour: {section}')
                )