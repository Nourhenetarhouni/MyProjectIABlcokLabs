#!/usr/bin/env python3
"""
Backend API Testing for Django Library Application
Tests the library functionality endpoints
"""

import requests
import sys
import json
from datetime import datetime

class DjangoLibraryTester:
    def __init__(self, base_url="http://localhost:8000"):
        self.base_url = base_url
        self.tests_run = 0
        self.tests_passed = 0
        self.session = requests.Session()

    def run_test(self, name, method, endpoint, expected_status, data=None, headers=None):
        """Run a single API test"""
        url = f"{self.base_url}/{endpoint.lstrip('/')}"
        
        if headers is None:
            headers = {}
        
        self.tests_run += 1
        print(f"\n🔍 Testing {name}...")
        print(f"   URL: {url}")
        
        try:
            if method == 'GET':
                response = self.session.get(url, headers=headers)
            elif method == 'POST':
                response = self.session.post(url, data=data, headers=headers)
            elif method == 'PUT':
                response = self.session.put(url, data=data, headers=headers)
            elif method == 'DELETE':
                response = self.session.delete(url, headers=headers)

            success = response.status_code == expected_status
            if success:
                self.tests_passed += 1
                print(f"✅ Passed - Status: {response.status_code}")
                if response.headers.get('content-type', '').startswith('application/json'):
                    try:
                        json_data = response.json()
                        print(f"   Response: {json.dumps(json_data, indent=2)[:200]}...")
                    except:
                        pass
                elif 'text/html' in response.headers.get('content-type', ''):
                    print(f"   HTML Response Length: {len(response.text)} chars")
            else:
                print(f"❌ Failed - Expected {expected_status}, got {response.status_code}")
                print(f"   Response: {response.text[:300]}...")

            return success, response

        except Exception as e:
            print(f"❌ Failed - Error: {str(e)}")
            return False, None

    def test_library_dashboard(self):
        """Test library dashboard page"""
        return self.run_test(
            "Library Dashboard",
            "GET",
            "client/library/",
            200
        )

    def test_document_list(self):
        """Test document list page"""
        return self.run_test(
            "Document List",
            "GET", 
            "client/library/documents/",
            200
        )

    def test_document_list_with_search(self):
        """Test document list with search parameters"""
        return self.run_test(
            "Document List with Search",
            "GET",
            "client/library/documents/?search=test&type=guideline&country=France",
            200
        )

    def test_document_list_pagination(self):
        """Test document list pagination"""
        return self.run_test(
            "Document List Pagination",
            "GET",
            "client/library/documents/?page=1",
            200
        )

    def test_api_search_documents(self):
        """Test API search endpoint"""
        return self.run_test(
            "API Search Documents",
            "GET",
            "client/library/api/search/?q=test&limit=5",
            200
        )

    def test_upload_document_page(self):
        """Test upload document page"""
        return self.run_test(
            "Upload Document Page",
            "GET",
            "client/library/upload/",
            200
        )

    def test_document_detail_existing(self):
        """Test document detail for existing validated document"""
        return self.run_test(
            "Document Detail (Existing - ID 65)",
            "GET",
            "client/library/documents/65/",
            200
        )

    def test_document_detail_existing_92(self):
        """Test document detail for existing validated document ID 92"""
        return self.run_test(
            "Document Detail (Existing - ID 92)",
            "GET",
            "client/library/documents/92/",
            200
        )

    def test_document_detail_nonexistent(self):
        """Test document detail for non-existent document"""
        return self.run_test(
            "Document Detail (Non-existent)",
            "GET",
            "client/library/documents/99999/",
            404
        )

    def test_download_document_nonexistent(self):
        """Test download for non-existent document"""
        return self.run_test(
            "Download Document (Non-existent)",
            "GET",
            "client/library/documents/99999/download/",
            404
        )

    def test_api_metadata_nonexistent(self):
        """Test API metadata for non-existent document"""
        return self.run_test(
            "API Metadata (Non-existent)",
            "GET",
            "client/library/api/documents/99999/metadata/",
            404
        )

    def test_documents_by_type(self):
        """Test documents filtered by type - NEW FEATURE"""
        return self.run_test(
            "Documents by Type (Guide)",
            "GET",
            "client/library/type/Guide/",
            200
        )

    def test_documents_by_type_with_filters(self):
        """Test documents by type with additional filters - NEW FEATURE"""
        return self.run_test(
            "Documents by Type with Filters",
            "GET",
            "client/library/type/Guide/?search=test&country=France&language=French",
            200
        )

    def test_documents_by_country(self):
        """Test documents filtered by country - NEW FEATURE"""
        return self.run_test(
            "Documents by Country (France)",
            "GET",
            "client/library/country/France/",
            200
        )

    def test_documents_by_country_with_filters(self):
        """Test documents by country with additional filters - NEW FEATURE"""
        return self.run_test(
            "Documents by Country with Filters",
            "GET",
            "client/library/country/France/?search=test&type=Guide&language=French",
            200
        )

    def test_documents_by_category(self):
        """Test documents filtered by source category - NEW FEATURE"""
        return self.run_test(
            "Documents by Category (EMA)",
            "GET",
            "client/library/category/ema/",
            200
        )

    def test_document_list_horizontal(self):
        """Test horizontal document list view - NEW FEATURE"""
        return self.run_test(
            "Document List Horizontal",
            "GET",
            "client/library/documents/horizontal/",
            200
        )

    def test_main_app_root(self):
        """Test main application root"""
        return self.run_test(
            "Main App Root",
            "GET",
            "",
            200
        )

    def test_client_dashboard(self):
        """Test client dashboard"""
        return self.run_test(
            "Client Dashboard",
            "GET",
            "client/",
            200
        )

def main():
    print("🚀 Starting Django Library Backend Tests")
    print("=" * 50)
    
    # Setup
    tester = DjangoLibraryTester("http://localhost:8000")
    
    # Run core functionality tests
    print("\n📋 Testing Core Library Functionality...")
    tester.test_main_app_root()
    tester.test_client_dashboard()
    tester.test_library_dashboard()
    tester.test_document_list()
    
    # Test search and filtering
    print("\n🔍 Testing Search and Filtering...")
    tester.test_document_list_with_search()
    tester.test_document_list_pagination()
    tester.test_api_search_documents()
    
    # Test upload functionality
    print("\n📤 Testing Upload Functionality...")
    tester.test_upload_document_page()
    
    # Test document detail functionality
    print("\n📄 Testing Document Detail Functionality...")
    tester.test_document_detail_existing()
    tester.test_document_detail_existing_92()
    
    # Test error handling
    print("\n⚠️ Testing Error Handling...")
    tester.test_document_detail_nonexistent()
    tester.test_download_document_nonexistent()
    tester.test_api_metadata_nonexistent()
    
    # Test NEW FILTERING FEATURES
    print("\n🆕 Testing New Filtering Features...")
    tester.test_documents_by_type()
    tester.test_documents_by_type_with_filters()
    tester.test_documents_by_country()
    tester.test_documents_by_country_with_filters()
    tester.test_documents_by_category()
    tester.test_document_list_horizontal()
    
    # Print results
    print("\n" + "=" * 50)
    print(f"📊 Test Results: {tester.tests_passed}/{tester.tests_run} tests passed")
    
    if tester.tests_passed == tester.tests_run:
        print("🎉 All tests passed!")
        return 0
    else:
        print(f"❌ {tester.tests_run - tester.tests_passed} tests failed")
        return 1

if __name__ == "__main__":
    sys.exit(main())