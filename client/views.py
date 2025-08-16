from django.shortcuts import render
from django.contrib.auth.decorators import login_required, user_passes_test

def is_client(user):
    return user.groups.filter(name="Client").exists()

@login_required(login_url='rawdocs:login')
@user_passes_test(is_client)
def client_dashboard(request):
    context = {
        'library_url': '/client/library/',
        'products_url': '/client/products/',
        'reports_url': '/client/reports/',
    }
    return render(request, 'client/dashboard.html', context)