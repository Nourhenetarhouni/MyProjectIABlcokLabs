from django.apps import AppConfig


class RawdocsConfig(AppConfig):
    default_auto_field = "django.db.models.BigAutoField"
    name = "rawdocs"
    
    def ready(self):
        import rawdocs.signals
