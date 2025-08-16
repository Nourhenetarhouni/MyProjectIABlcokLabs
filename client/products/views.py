from django.shortcuts import render, get_object_or_404, redirect
from django.http import JsonResponse, HttpResponse
from django.views.decorators.csrf import csrf_exempt
from django.views.decorators.http import require_http_methods
from django.utils.decorators import method_decorator
from django.views.generic import View
from rest_framework import generics, status
from rest_framework.decorators import api_view
from rest_framework.response import Response
from .models import Product, ProductSpecification, ManufacturingSite, ProductVariation
from .serializers import ProductListSerializer, ProductDetailSerializer
import json
import logging

logger = logging.getLogger(__name__)

def products_list_view(request):
    """Vue principale des produits"""
    return render(request, 'client/products/products_list.html')

def product_detail_view(request, pk):
    """Vue détail d'un produit"""
    product = get_object_or_404(Product, pk=pk)
    return render(request, 'client/products/product_detail.html', {'product': product})

class ProductListAPIView(generics.ListCreateAPIView):
    serializer_class = ProductListSerializer
    
    def get_queryset(self):
        queryset = Product.objects.all().order_by('-created_at')
        search = self.request.GET.get('search', '')
        
        if search:
            queryset = queryset.filter(
                name__icontains=search
            ) | queryset.filter(
                active_ingredient__icontains=search
            )
        
        return queryset
    
    def create(self, request, *args, **kwargs):
        """Create a new product with all related data"""
        try:
            
            data = request.data
                
            logger.info(f"Creating product with data: {data}")
            
            # Extract product data
            product_data = data.get('product', {})
            regulatory_data = data.get('regulatory', {})
            sites_data = data.get('sites', [])
            
            # Create product
            product_serializer = ProductListSerializer(data=product_data)
            if product_serializer.is_valid():
                product = product_serializer.save()
                logger.info(f"Product created with ID: {product.id}")
                
                # Create regulatory specification only if we have the required fields
                if (regulatory_data and 
                    regulatory_data.get('renewal_date') and 
                    regulatory_data.get('approval_date')):
                    
                    from datetime import datetime
                    
                    # Parse date strings to date objects
                    approval_date = None
                    renewal_date = None
                    
                    if regulatory_data.get('approval_date'):
                        approval_date = datetime.strptime(regulatory_data.get('approval_date'), '%Y-%m-%d').date()
                    
                    if regulatory_data.get('renewal_date'):
                        renewal_date = datetime.strptime(regulatory_data.get('renewal_date'), '%Y-%m-%d').date()
                    
                    spec = ProductSpecification.objects.create(
                        product=product,
                        country_code=regulatory_data.get('country_code', 'FR'),
                        amm_number=regulatory_data.get('amm_number', ''),
                        approval_date=approval_date,
                        renewal_date=renewal_date,
                        ctd_dossier_complete=regulatory_data.get('ctd_dossier_complete', False),
                        gmp_certificate=regulatory_data.get('gmp_certificate', False),
                        inspection_report=regulatory_data.get('inspection_report', False),
                        rcp_etiquetage=regulatory_data.get('rcp_etiquetage', False),
                    )
                    logger.info(f"Regulatory spec created for product {product.id}")
                # Create manufacturing sites if provided
                for site_data in sites_data:
                    if site_data.get('country') and site_data.get('city') and site_data.get('site_name'):
                        site = ManufacturingSite.objects.create(
                            product=product,
                            country=site_data['country'],
                            city=site_data['city'],
                            site_name=site_data['site_name'],
                            gmp_certified=site_data.get('gmp_certified', False)
                        )
                        logger.info(f"Site created: {site.site_name} for product {product.id}")
                
                # Return the product in the same format as the list
                response_data = {
                    'id': product.id,
                    'name': product.name,
                    'active_ingredient': product.active_ingredient,
                    'dosage': product.dosage,
                    'form': product.form,
                    'therapeutic_area': product.therapeutic_area,
                    'status': product.status,
                    'created_at': product.created_at.isoformat(),
                    'updated_at': product.updated_at.isoformat(),
                }
                
                return Response(response_data, status=status.HTTP_201_CREATED)
            else:
                logger.error(f"Product validation failed: {product_serializer.errors}")
                return Response(
                    {'errors': product_serializer.errors},
                    status=status.HTTP_400_BAD_REQUEST
                )
                
        except Exception as e:
            logger.error(f"Error creating product: {str(e)}")
            return Response(
                {'error': f'Erreur lors de la création du produit: {str(e)}'},
                status=status.HTTP_500_INTERNAL_SERVER_ERROR
            )

class ProductDetailAPIView(generics.RetrieveAPIView):
    queryset = Product.objects.all()
    serializer_class = ProductDetailSerializer

@api_view(['GET'])
def search_products(request):
    """Search products"""
    query = request.GET.get('q', '')
    if query:
        products = Product.objects.filter(
            name__icontains=query
        ) | Product.objects.filter(
            active_ingredient__icontains=query
        )
    else:
        products = Product.objects.all()
    
    serializer = ProductListSerializer(products, many=True)
    return Response(serializer.data)

@api_view(['GET'])
def product_overview(request, pk):
    """API pour l'onglet Vue d'ensemble"""
    try:
        product = get_object_or_404(Product, pk=pk)
        specifications = ProductSpecification.objects.filter(product=product)
        
        logger.info(f"Loading overview for product {pk}")
        
        data = {
            'product': {
                'id': product.id,
                'name': product.name,
                'active_ingredient': product.active_ingredient,
                'dosage': product.dosage,
                'form': product.form,
                'therapeutic_area': product.therapeutic_area,
                'status': product.status,
                'source_document': product.source_document.id if product.source_document else None, 
                'created_at': product.created_at.isoformat(),
                'updated_at': product.updated_at.isoformat(),
            },
            'specifications': [
                {
                    'country': spec.country_code,
                    'amm_number': spec.amm_number,
                    'approval_date': spec.approval_date.isoformat() if spec.approval_date else None,
                    'renewal_date': spec.renewal_date.isoformat() if spec.renewal_date else None,
                    'documents': {
                        'ctd_dossier_complete': spec.ctd_dossier_complete,
                        'gmp_certificate': spec.gmp_certificate,
                        'inspection_report': spec.inspection_report,
                        'rcp_etiquetage': spec.rcp_etiquetage,
                    }
                }
                for spec in specifications
            ]
        }
        
        logger.info(f"Overview data for product {pk}: {len(data['specifications'])} specifications")
        return Response(data)
        
    except Product.DoesNotExist:
        logger.error(f"Product {pk} not found")
        return Response(
            {'error': 'Produit non trouvé'}, 
            status=status.HTTP_404_NOT_FOUND
        )
    except Exception as e:
        logger.error(f"Error loading overview for product {pk}: {str(e)}")
        return Response(
            {'error': str(e)}, 
            status=status.HTTP_500_INTERNAL_SERVER_ERROR
        )

@api_view(['GET'])
def product_sites(request, pk):
    """API pour l'onglet Sites"""
    try:
        product = get_object_or_404(Product, pk=pk)
        sites = ManufacturingSite.objects.filter(product=product)
        
        logger.info(f"Loading sites for product {pk}: {sites.count()} sites found")
        
        data = [
            {
                'id': site.id,
                'country': site.country,
                'city': site.city,
                'site_name': site.site_name,
                'gmp_certified': site.gmp_certified,
                'gmp_expiry': site.gmp_expiry.isoformat() if site.gmp_expiry else None,
                'last_audit': site.last_audit.isoformat() if site.last_audit else None,
            }
            for site in sites
        ]
        
        return Response(data)
        
    except Product.DoesNotExist:
        logger.error(f"Product {pk} not found")
        return Response(
            {'error': 'Produit non trouvé'}, 
            status=status.HTTP_404_NOT_FOUND
        )
    except Exception as e:
        logger.error(f"Error loading sites for product {pk}: {str(e)}")
        return Response(
            {'error': str(e)}, 
            status=status.HTTP_500_INTERNAL_SERVER_ERROR
        )

@api_view(['GET'])
def product_variations(request, pk):
    """API pour l'onglet Variations"""
    try:
        product = get_object_or_404(Product, pk=pk)
        variations = ProductVariation.objects.filter(product=product).order_by('-submission_date')
        
        logger.info(f"Loading variations for product {pk}: {variations.count()} variations found")
        
        data = [
            {
                'id': var.id,
                'variation_type': var.variation_type,
                'title': var.title,
                'description': var.description,
                'submission_date': var.submission_date.isoformat() if var.submission_date else None,
                'approval_date': var.approval_date.isoformat() if var.approval_date else None,
                'status': var.status,
            }
            for var in variations
        ]
        
        return Response(data)
        
    except Product.DoesNotExist:
        logger.error(f"Product {pk} not found")
        return Response(
            {'error': 'Produit non trouvé'}, 
            status=status.HTTP_404_NOT_FOUND
        )
    except Exception as e:
        logger.error(f"Error loading variations for product {pk}: {str(e)}")
        return Response(
            {'error': str(e)}, 
            status=status.HTTP_500_INTERNAL_SERVER_ERROR
        )
    

def product_source_document_view(request, pk):
    """View to display the source document for a product"""
    product = get_object_or_404(Product, pk=pk)
    
    # Check if product has a source document
    if hasattr(product, 'source_document') and product.source_document:
        document = product.source_document
        
        # Check if document file exists
        if document.file:
            try:
                # Serve the PDF file directly in browser
                response = HttpResponse(document.file.read(), content_type='application/pdf')
                response['Content-Disposition'] = f'inline; filename="{document.file.name}"'
                return response
            except:
                # If file doesn't exist, show error
                return HttpResponse(
                    "<html><body><h2>Erreur</h2>"
                    "<p>Le fichier PDF n'a pas pu être chargé.</p>"
                    "<script>window.close();</script></body></html>"
                )
        else:
            return HttpResponse(
                "<html><body><h2>Aucun fichier disponible</h2>"
                "<p>Ce document n'a pas de fichier PDF associé.</p>"
                "<script>window.close();</script></body></html>"
            )
    else:
        # Return a simple message if no source document exists
        return HttpResponse(
            "<html><body><h2>Aucun document source disponible</h2>"
            "<p>Ce produit n'a pas de document source associé.</p>"
            "<script>window.close();</script></body></html>"
        )
    
@api_view(['POST'])
def add_product_variation(request, pk):
    """API pour ajouter une nouvelle variation"""
    try:
        product = get_object_or_404(Product, pk=pk)
        
        # Get data from request
        data = request.data
        
        # Parse the submission_date string to a date object
        submission_date = None
        if data.get('submission_date'):
            from datetime import datetime
            submission_date = datetime.strptime(data.get('submission_date'), '%Y-%m-%d').date()
        
        # Create the variation
        variation = ProductVariation.objects.create(
            product=product,
            variation_type=data.get('variation_type'),
            title=data.get('title', ''),
            description=data.get('description', ''),
            submission_date=submission_date,  # Now it's a date object
            status='soumis'  # Default status
        )
        
        logger.info(f"Variation created for product {pk}: {variation.title}")
        
        # Return the created variation
        response_data = {
            'id': variation.id,
            'variation_type': variation.variation_type,
            'title': variation.title,
            'description': variation.description,
            'submission_date': variation.submission_date.isoformat() if variation.submission_date else None,
            'approval_date': variation.approval_date.isoformat() if variation.approval_date else None,
            'status': variation.status,
        }
        
        return Response(response_data, status=status.HTTP_201_CREATED)
        
    except Exception as e:
        logger.error(f"Error creating variation for product {pk}: {str(e)}")
        return Response(
            {'error': str(e)}, 
            status=status.HTTP_500_INTERNAL_SERVER_ERROR
        )