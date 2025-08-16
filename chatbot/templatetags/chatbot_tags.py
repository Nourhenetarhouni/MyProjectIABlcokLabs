from django import template
from django.template.loader import render_to_string

register = template.Library()

@register.simple_tag
def chatbot_widget():
    return render_to_string('chatbot/chatbot_widget.html')
