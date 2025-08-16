
from django.contrib import admin
from django.conf import settings
from django.conf.urls.static import static
from django.urls import path, include

urlpatterns = [
    path('admin/', admin.site.urls),
    path('', include('rawdocs.urls')),
    path('expert/', include('expert.urls')),
    path('client/', include('client.urls')),
    path('submissions/', include('submissions.urls', namespace='submissions')),
    path('chatbot/', include('chatbot.urls')),
]

if settings.DEBUG:
    urlpatterns += static(settings.MEDIA_URL, document_root=settings.MEDIA_ROOT)
