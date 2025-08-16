from rest_framework import serializers
from .models import Product, ProductSpecification, ManufacturingSite, ProductVariation

class ProductListSerializer(serializers.ModelSerializer):
    class Meta:
        model = Product
        fields = ['id', 'name', 'active_ingredient', 'status', 'dosage', 'form']

class ProductSpecificationSerializer(serializers.ModelSerializer):
    class Meta:
        model = ProductSpecification
        fields = '__all__'

class ManufacturingSiteSerializer(serializers.ModelSerializer):
    class Meta:
        model = ManufacturingSite
        fields = '__all__'

class ProductVariationSerializer(serializers.ModelSerializer):
    class Meta:
        model = ProductVariation
        fields = '__all__'

class ProductDetailSerializer(serializers.ModelSerializer):
    specifications = ProductSpecificationSerializer(many=True, read_only=True)
    sites = ManufacturingSiteSerializer(many=True, read_only=True)
    variations = ProductVariationSerializer(many=True, read_only=True)
    
    class Meta:
        model = Product
        fields = '__all__'