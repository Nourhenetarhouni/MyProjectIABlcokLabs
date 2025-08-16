# rawdocs/migrations/0002_create_roles.py
from django.db import migrations

def create_roles(apps, schema_editor):
    Group = apps.get_model('auth', 'Group')
    for name in ['Metadonneur', 'Annotateur', 'Expert']:
        Group.objects.get_or_create(name=name)

def delete_roles(apps, schema_editor):
    Group = apps.get_model('auth', 'Group')
    Group.objects.filter(name__in=['Metadonneur', 'Annotateur', 'Expert']).delete()

class Migration(migrations.Migration):

    dependencies = [
        ('rawdocs', '0001_initial'),
        ('auth',    '0012_alter_user_first_name_max_length'),
    ]

    operations = [
        migrations.RunPython(create_roles, delete_roles),
    ]
