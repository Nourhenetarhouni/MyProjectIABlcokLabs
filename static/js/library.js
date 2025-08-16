// Library JavaScript functionality

document.addEventListener('DOMContentLoaded', function() {
    initializeSearch();
    initializeDocumentCards();
});

function initializeSearch() {
    const searchInput = document.getElementById('global-search');
    const searchResults = document.getElementById('search-results');
    let searchTimeout;

    if (!searchInput) return;

    searchInput.addEventListener('input', function() {
        const query = this.value.trim();
        
        // Clear previous timeout
        clearTimeout(searchTimeout);
        
        if (query.length < 2) {
            hideSearchResults();
            return;
        }

        // Debounce search
        searchTimeout = setTimeout(() => {
            performSearch(query);
        }, 300);
    });

    searchInput.addEventListener('focus', function() {
        if (this.value.trim().length >= 2) {
            showSearchResults();
        }
    });

    // Hide search results when clicking outside
    document.addEventListener('click', function(e) {
        if (!e.target.closest('.floating-search')) {
            hideSearchResults();
        }
    });

    function performSearch(query) {
        fetch(`/library/api/search/?q=${encodeURIComponent(query)}&limit=8`)
            .then(response => response.json())
            .then(data => {
                displaySearchResults(data);
            })
            .catch(error => {
                console.error('Search error:', error);
                hideSearchResults();
            });
    }

    function displaySearchResults(results) {
        if (results.length === 0) {
            searchResults.innerHTML = '<div class="search-result-item">Aucun document trouvé</div>';
        } else {
            const html = results.map(doc => `
                <div class="search-result-item" onclick="location.href='/library/documents/${doc.id}/'">
                    <div style="font-weight: 500; margin-bottom: 4px;">${doc.title}</div>
                    <div style="font-size: 0.8rem; color: #64748b;">
                        ${doc.authority} • ${doc.type}
                        ${doc.publication_date ? '• ' + new Date(doc.publication_date).toLocaleDateString('fr-FR') : ''}
                    </div>
                </div>
            `).join('');
            searchResults.innerHTML = html;
        }
        showSearchResults();
    }

    function showSearchResults() {
        searchResults.style.display = 'block';
    }

    function hideSearchResults() {
        searchResults.style.display = 'none';
    }
}

function initializeDocumentCards() {
    // Add click handlers for document cards
    const documentCards = document.querySelectorAll('.document-card');
    
    documentCards.forEach(card => {
        card.addEventListener('click', function(e) {
            // Don't navigate if clicking on a button or link inside
            if (e.target.closest('button') || e.target.closest('a')) {
                return;
            }
            
            const url = this.getAttribute('onclick');
            if (url) {
                // Extract URL from onclick attribute
                const match = url.match(/location\.href='([^']+)'/);
                if (match) {
                    window.location.href = match[1];
                }
            }
        });
    });
}

// Utility functions
function formatFileSize(bytes) {
    if (bytes === 0) return '0 B';
    const k = 1024;
    const sizes = ['B', 'KB', 'MB', 'GB'];
    const i = Math.floor(Math.log(bytes) / Math.log(k));
    return parseFloat((bytes / Math.pow(k, i)).toFixed(1)) + ' ' + sizes[i];
}

function formatDate(dateString) {
    const date = new Date(dateString);
    return date.toLocaleDateString('fr-FR', {
        year: 'numeric',
        month: 'long',
        day: 'numeric'
    });
}

// Export functions for use in other scripts
window.LibraryJS = {
    formatFileSize,
    formatDate
};