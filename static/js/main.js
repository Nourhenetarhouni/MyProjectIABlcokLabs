// Configuration globale
const CONFIG = {
    API_BASE: '/api/products/',
    ENDPOINTS: {
        list: 'api/products/',
        detail: 'api/products/{id}/',
        search: 'api/products/search/',
        overview: 'api/products/{id}/overview/',
        sites: 'api/products/{id}/sites/',
        variations: 'api/products/{id}/variations/',
    }
};

// Utilitaires
const Utils = {
    formatDate: (dateString) => {
        if (!dateString) return 'N/A';
        const date = new Date(dateString);
        return date.toLocaleDateString('fr-FR');
    },
    
    debounce: (func, delay) => {
        let timeoutId;
        return (...args) => {
            clearTimeout(timeoutId);
            timeoutId = setTimeout(() => func.apply(null, args), delay);
        };
    },
    
    showNotification: (message, type = 'info') => {
        // Implémentation simple de notification
        const notification = document.createElement('div');
        notification.className = `notification notification-${type}`;
        notification.textContent = message;
        document.body.appendChild(notification);
        
        setTimeout(() => {
            notification.remove();
        }, 3000);
    }
};

// API Helper
const API = {
    async request(url, options = {}) {
        try {
            const response = await fetch(url, {
                headers: {
                    'Content-Type': 'application/json',
                    'X-CSRFToken': this.getCSRFToken(),
                    ...options.headers
                },
                ...options
            });
            
            if (!response.ok) {
                throw new Error(`HTTP error! status: ${response.status}`);
            }
            
            return await response.json();
        } catch (error) {
            console.error('API request failed:', error);
            Utils.showNotification('Erreur de connexion', 'error');
            throw error;
        }
    },
    
    getCSRFToken() {
        const token = document.querySelector('[name=csrfmiddlewaretoken]');
        return token ? token.value : '';
    },
    
    // Méthodes spécifiques
    async getProducts() {
        return this.request('/api/products/');
    },
    
    async searchProducts(query) {
        return this.request(`/api/products/search/?q=${encodeURIComponent(query)}`);
    },
    
    async getProductOverview(id) {
        return this.request(`/api/products/${id}/overview/`);
    },
    
    async getProductSites(id) {
        return this.request(`/api/products/${id}/sites/`);
    },
    
    async getProductVariations(id) {
        return this.request(`/api/products/${id}/variations/`);
    }
};

// Export global pour utilisation dans d'autres scripts
window.RegXApp = {
    CONFIG,
    Utils,
    API
};