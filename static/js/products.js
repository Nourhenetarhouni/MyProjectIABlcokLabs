// Products App 
class ProductsApp {
    constructor() {
        this.currentProductId = null;
        this.currentTab = 'overview';
        this.products = [];
        this.siteCounter = 0;
        
        this.init();
    }
    
    init() {
        this.bindElements();
        this.bindEvents();
        this.loadProducts();
    }
    
    bindElements() {
        this.elements = {
            productsList: document.getElementById('products-list'),
            productTitle: document.getElementById('product-title'),
            tabContent: document.getElementById('tab-content'),
            searchInput: document.getElementById('search-input'),
            tabButtons: document.querySelectorAll('.tab-button'),
            newProductBtn: document.getElementById('new-product-btn'),
            modal: document.getElementById('add-product-modal'),
            form: document.getElementById('add-product-form'),
            closeModal: document.getElementById('close-modal'),
            cancelBtn: document.getElementById('cancel-btn'),
            saveBtn: document.getElementById('save-btn'),
            addSiteBtn: document.getElementById('add-site-btn'),
            sitesContainer: document.getElementById('sites-container')
        };
    }
    
    bindEvents() {
        // Tab events
        this.elements.tabButtons.forEach(button => {
            button.addEventListener('click', (e) => {
                const tab = e.target.getAttribute('data-tab');
                this.switchTab(tab);
            });
        });
        
        // Search events
        this.elements.searchInput?.addEventListener('input', (e) => {
            this.handleSearch(e.target.value);
        });
        
        // Modal events
        this.elements.newProductBtn?.addEventListener('click', () => {
            this.showModal();
        });
        
        this.elements.closeModal?.addEventListener('click', () => {
            this.hideModal();
        });
        
        this.elements.cancelBtn?.addEventListener('click', () => {
            this.hideModal();
        });
        
        this.elements.modal?.addEventListener('click', (e) => {
            if (e.target === this.elements.modal) {
                this.hideModal();
            }
        });
        
        this.elements.form?.addEventListener('submit', (e) => {
            e.preventDefault();
            this.submitForm();
        });
        
        this.elements.addSiteBtn?.addEventListener('click', () => {
            this.addSiteForm();
        });
    }
    
    async loadProducts() {
        try {
            console.log('Loading products...');
            const response = await fetch('/client/products/api/products/');
            
            if (response.ok) {
                const data = await response.json();
                // Handle both paginated and non-paginated responses
                this.products = data.results || data;
                console.log('Products loaded:', this.products);
                
                this.renderProducts(this.products);
                
                // Select first product if none selected and products exist
                if (!this.currentProductId && this.products.length > 0) {
                    this.selectProduct(this.products[0].id);
                }
            } else {
                console.error('Failed to load products:', response.status);
                this.loadFallbackProducts();
            }
        } catch (error) {
            console.error('Error loading products:', error);
            this.loadFallbackProducts();
        }
    }
    
    loadFallbackProducts() {
        console.log('Loading fallback products...');
        this.products = [
            {
                id: 1,
                name: "RegXpirin 500mg",
                active_ingredient: "Analgésique",
                status: "commercialise",
                dosage: "500mg",
                form: "Comprimé",
                therapeutic_area: "Cardiovascular"
            },
            {
                id: 2,
                name: "RegXcillin 250mg",
                active_ingredient: "Antibactérial",
                status: "developpement",
                dosage: "250mg",
                form: "Gélule",
                therapeutic_area: "Anti-infectieux"
            }
        ];
        
        this.renderProducts(this.products);
        this.selectProduct(1);
    }
    
    renderProducts(products) {
        console.log('Rendering products:', products);
        
        if (!this.elements.productsList) {
            console.error('Products list element not found');
            return;
        }
        
        if (!products || products.length === 0) {
            this.elements.productsList.innerHTML = `
                <div class="empty-state">
                    <i class="material-icons">inventory</i>
                    <h3>Aucun produit</h3>
                    <p>Cliquez sur "Nouveau Produit" pour ajouter votre premier produit</p>
                </div>
            `;
            return;
        }
        
        this.elements.productsList.innerHTML = products.map(product => `
            <div class="product-item" data-product-id="${product.id}">
                <div class="product-name">${product.name}</div>
                <div class="product-ingredient">${product.active_ingredient}</div>
                <div class="product-dosage">${product.dosage || ''}</div>
                <span class="product-status status-${product.status}">${this.getStatusLabel(product.status)}</span>
            </div>
        `).join('');
        
        // Bind click events to product items
        this.elements.productsList.querySelectorAll('.product-item').forEach(item => {
            item.addEventListener('click', (e) => {
                const productId = parseInt(item.getAttribute('data-product-id'));
                console.log('Product clicked:', productId);
                this.selectProduct(productId);
            });
        });
    }
    
    selectProduct(productId) {
        console.log('Selecting product ID:', productId);
        
        // Update visual selection
        this.elements.productsList?.querySelectorAll('.product-item').forEach(item => {
            item.classList.remove('active');
        });
        
        const selectedItem = this.elements.productsList?.querySelector(`[data-product-id="${productId}"]`);
        if (selectedItem) {
            selectedItem.classList.add('active');
        }
        
        // Update title
        const product = this.products.find(p => p.id === productId);
        if (product && this.elements.productTitle) {
            this.elements.productTitle.textContent = product.name;
        }
        
        // Store current product ID
        this.currentProductId = productId;
        
        // Load content for current tab
        this.loadTabContent(this.currentTab);
    }
    
    switchTab(tabName) {
        console.log('Switching to tab:', tabName);
        
        this.elements.tabButtons.forEach(btn => {
            btn.classList.remove('active');
            if (btn.getAttribute('data-tab') === tabName) {
                btn.classList.add('active');
            }
        });
        
        this.currentTab = tabName;
        this.loadTabContent(tabName);
    }
    
    async loadTabContent(tabName) {
        if (!this.elements.tabContent || !this.currentProductId) {
            console.log('Cannot load tab content: missing elements or product ID');
            return;
        }
        
        console.log(`Loading tab content: ${tabName} for product ${this.currentProductId}`);
        
        // Show loading state
        this.elements.tabContent.innerHTML = `
            <div class="loading">
                <i class="material-icons">hourglass_empty</i>
                <p>Chargement...</p>
            </div>
        `;
        
        try {
            switch (tabName) {
                case 'overview':
                    await this.loadOverviewTab();
                    break;
                case 'sites':
                    await this.loadSitesTab();
                    break;
                case 'variations':
                    await this.loadVariationsTab();
                    break;
                case 'regulatory':
                    await this.loadRegulatoryTab();
                    break;
                default:
                    console.log('Unknown tab:', tabName);
            }
        } catch (error) {
            console.error(`Error loading ${tabName} tab:`, error);
            this.elements.tabContent.innerHTML = `
                <div class="empty-state">
                    <i class="material-icons">error</i>
                    <h3>Erreur de chargement</h3>
                    <p>Impossible de charger les données pour ce produit</p>
                </div>
            `;
        }
    }
    
    async loadOverviewTab() {
        console.log(`Loading overview for product ${this.currentProductId}`);
        
        try {
            const response = await fetch(`/client/products/api/products/${this.currentProductId}/overview/`);
            
            if (response.ok) {
                const data = await response.json();
                console.log('Overview data:', data);
                
                const product = data.product;
                const spec = data.specifications && data.specifications.length > 0 ? data.specifications[0] : null;
                
                this.elements.tabContent.innerHTML = `
                    <div class="regulatory-content">
                        <div class="regulatory-info">
                            <div class="regulatory-item">
                                <span class="regulatory-label">Nom du produit</span>
                                <span class="regulatory-value">${product.name}</span>
                            </div>
                            <div class="regulatory-item">
                                <span class="regulatory-label">Type</span>
                                <span class="regulatory-value">${product.form}</span>
                            </div>
                            <div class="regulatory-item">
                                <span class="regulatory-label">Principe actif</span>
                                <span class="regulatory-value">${product.active_ingredient}</span>
                            </div>
                            <div class="regulatory-item">
                                <span class="regulatory-label">Dosage</span>
                                <span class="regulatory-value">${product.dosage}</span>
                            </div>
                            <div class="regulatory-item">
                                <span class="regulatory-label">Statut</span>
                                <span class="regulatory-value">
                                    <span class="status-badge status-${product.status}">${this.getStatusLabel(product.status)}</span>
                                </span>
                            </div>
                            <div class="regulatory-item">
                                <span class="regulatory-label">Zone thérapeutique</span>
                                <span class="regulatory-value">${product.therapeutic_area}</span>
                            </div>
                            ${spec ? `
                            <div class="regulatory-item">
                                <span class="regulatory-label">N° AMM</span>
                                <span class="regulatory-value">${spec.amm_number}</span>
                            </div>
                            <div class="regulatory-item">
                                <span class="regulatory-label">Date d'approbation</span>
                                <span class="regulatory-value">${this.formatDate(spec.approval_date)}</span>
                            </div>
                            <div class="regulatory-item">
                                <span class="regulatory-label">Prochain renouvellement</span>
                                <span class="regulatory-value">${this.formatDate(spec.renewal_date)}</span>
                            </div>
                            ` : ''}
                        </div>
                    </div>
                `;
            } else {
                // Fallback to local product data
                console.log('API failed, using local product data');
                this.loadOverviewFromLocalData();
            }
        } catch (error) {
            console.error('Error loading overview:', error);
            this.loadOverviewFromLocalData();
        }
    }
    
    loadOverviewFromLocalData() {
        const product = this.products.find(p => p.id === this.currentProductId);
        if (product) {
            this.elements.tabContent.innerHTML = `
                <div class="regulatory-content">
                    <div class="regulatory-info">
                        <div class="regulatory-item">
                            <span class="regulatory-label">Nom du produit</span>
                            <span class="regulatory-value">${product.name}</span>
                        </div>
                        <div class="regulatory-item">
                            <span class="regulatory-label">Type</span>
                            <span class="regulatory-value">${product.form || 'N/A'}</span>
                        </div>
                        <div class="regulatory-item">
                            <span class="regulatory-label">Principe actif</span>
                            <span class="regulatory-value">${product.active_ingredient}</span>
                        </div>
                        <div class="regulatory-item">
                            <span class="regulatory-label">Dosage</span>
                            <span class="regulatory-value">${product.dosage || 'N/A'}</span>
                        </div>
                        <div class="regulatory-item">
                            <span class="regulatory-label">Statut</span>
                            <span class="regulatory-value">
                                <span class="status-badge status-${product.status}">${this.getStatusLabel(product.status)}</span>
                            </span>
                        </div>
                        <div class="regulatory-item">
                            <span class="regulatory-label">Zone thérapeutique</span>
                            <span class="regulatory-value">${product.therapeutic_area || 'N/A'}</span>
                        </div>
                    </div>
                </div>
            `;
        }
    }
    
    async loadSitesTab() {
    console.log(`Loading sites for product ${this.currentProductId}`);
    
    try {
        const response = await fetch(`/client/products/api/products/${this.currentProductId}/sites/`);
        
        if (response.ok) {
            const sites = await response.json();
            console.log('Sites data:', sites);
            
            this.elements.tabContent.innerHTML = `
                <div class="sites-header">
                    <h3>Sites de Production (${sites.length})</h3>
                    <div class="sites-actions">
                        <button class="btn btn-secondary" onclick="window.productsApp.viewSites()">
                            <i class="material-icons">visibility</i>
                            Voir Sites
                        </button>
                        <button class="btn btn-secondary" onclick="window.productsApp.editSites()">
                            <i class="material-icons">edit</i>
                            Modifier Sites
                        </button>
                        <button class="btn btn-primary" onclick="window.productsApp.addSite()">
                            <i class="material-icons">add</i>
                            Ajouter un site
                        </button>
                    </div>
                </div>
                
                ${sites.length === 0 ? `
                    <div class="empty-state">
                        <i class="material-icons">location_off</i>
                        <h3>Aucun site de production</h3>
                        <p>Aucun site n'est configuré pour ce produit</p>
                    </div>
                ` : `
                    <div class="sites-list">
                        ${sites.map(site => `
                            <div class="site-item">
                                <div class="site-info">
                                    <i class="material-icons">factory</i>
                                    <div>
                                        <div class="site-name">${site.site_name || 'Nom non défini'}</div>
                                        <div class="site-location">${site.city}, ${site.country}</div>
                                    </div>
                                    ${site.gmp_certified ? '<span class="gmp-badge">GMP Certifié</span>' : ''}
                                </div>
                                <div class="site-actions">
                                    <button class="btn btn-sm btn-outline" onclick="window.productsApp.editSingleSite(${site.id})">
                                        <i class="material-icons">edit</i>
                                    </button>
                                    <button class="btn btn-sm btn-danger" onclick="window.productsApp.deleteSite(${site.id})">
                                        <i class="material-icons">delete</i>
                                    </button>
                                </div>
                            </div>
                        `).join('')}
                    </div>
                `}
            `;
        } else {
            throw new Error('Failed to load sites');
        }
    } catch (error) {
        console.error('Error loading sites:', error);
        this.elements.tabContent.innerHTML = `
            <div class="sites-header">
                <h3>Sites de Production</h3>
                <button class="btn btn-primary" onclick="window.productsApp.addSite()">
                    <i class="material-icons">add</i>
                    Ajouter un site
                </button>
            </div>
            <div class="empty-state">
                <i class="material-icons">location_off</i>
                <h3>Aucun site de production</h3>
                <p>Aucun site n'est configuré pour ce produit</p>
            </div>
        `;
    }
}
    
async loadVariationsTab() {
    console.log(`Loading variations for product ${this.currentProductId}`);
    const variationsHeader = `
        <div class="sites-header">
            <h3>Variations du Produit</h3>
            <button class="btn btn-primary" onclick="document.getElementById('addVariationModal').style.display='flex'; document.body.style.overflow='hidden';">
                <i class="material-icons">add</i>
                Nouvelle Variation
            </button>
        </div>
    `;
    
    try {
        const response = await fetch(`/client/products/api/products/${this.currentProductId}/variations/`);
        
        if (response.ok) {
            const variations = await response.json();
            console.log('Variations data:', variations);
            
            if (variations.length === 0) {
                this.elements.tabContent.innerHTML = `
                    ${variationsHeader}
                    <div class="empty-state">
                        <i class="material-icons">timeline</i>
                        <h3>Aucune variation</h3>
                        <p>Aucune variation n'a été soumise pour ce produit</p>
                    </div>
                `;
                return;
            }

            this.elements.tabContent.innerHTML = `
                ${variationsHeader}
                <div class="variations-timeline">
                    ${variations.map(variation => `
                        <div class="variation-item">
                            <div class="variation-type">${variation.variation_type?.split('_')[1]?.toUpperCase() || 'N/A'}</div>
                            <div class="variation-content">
                                <div class="variation-title">${variation.title}</div>
                                <div class="variation-date">${this.formatDate(variation.submission_date)}</div>
                                <div class="variation-description">${variation.description || ''}</div>
                                <span class="variation-status status-${variation.status}">${this.getStatusLabel(variation.status)}</span>
                            </div>
                        </div>
                    `).join('')}
                </div>
            `;
        } else {
            throw new Error('Failed to load variations');
        }
    } catch (error) {
        console.error('Error loading variations:', error);
        this.elements.tabContent.innerHTML = `
            ${variationsHeader}
            <div class="empty-state">
                <i class="material-icons">timeline</i>
                <h3>Aucune variation</h3>
                <p>Aucune variation n'a été soumise pour ce produit</p>
            </div>
        `;
    }
}
    
    async loadRegulatoryTab() {
        console.log(`Loading regulatory for product ${this.currentProductId}`);
        
        try {
            const response = await fetch(`/client/products/api/products/${this.currentProductId}/overview/`);
            
            if (response.ok) {
                const data = await response.json();
                const spec = data.specifications && data.specifications.length > 0 ? data.specifications[0] : null;
                
                this.elements.tabContent.innerHTML = `
                    <div class="overview-grid">
                        <div class="info-section">
                            <h3 class="info-title">Informations Réglementaires</h3>
                            ${spec ? `
                            <div class="info-item">
                                <span class="info-label">Numéro AMM</span>
                                <span class="info-value">${spec.amm_number}</span>
                            </div>
                            <div class="info-item">
                                <span class="info-label">Date d'approbation</span>
                                <span class="info-value">${this.formatDate(spec.approval_date)}</span>
                            </div>
                            <div class="info-item">
                                <span class="info-label">Prochain renouvellement</span>
                                <span class="info-value">${this.formatDate(spec.renewal_date)}</span>
                            </div>
                            ` : '<p>Aucune information réglementaire disponible</p>'}
                        </div>
                        
                        <div class="info-section">
                            <h3 class="info-title">Documents Associés</h3>
                            <div class="document-item">
                                <span class="document-name">Dossier CTD complet</span>
                                <div class="document-status">
                                    ${data.product.source_document ? `
                                        <button class="view-document-btn" onclick="window.productsApp.viewSourceDocument(${this.currentProductId})">
                                            <i class="material-icons">visibility</i>
                                        </button>
                                    ` : '<span class="no-document">-</span>'}
                                </div>
                            </div>
                        </div>
                                            </div>
                `;
            } else {
                throw new Error('Failed to load regulatory data');
            }
        } catch (error) {
            console.error('Error loading regulatory:', error);
            this.elements.tabContent.innerHTML = `
                <div class="empty-state">
                    <i class="material-icons">gavel</i>
                    <h3>Aucune information réglementaire</h3>
                    <p>Aucune donnée réglementaire disponible pour ce produit</p>
                </div>
            `;
        }
    }
    
    // Modal functions
    showModal() {
        if (this.elements.modal) {
            this.elements.modal.style.display = 'flex';
            document.body.style.overflow = 'hidden';
        }
    }
    
    hideModal() {
        if (this.elements.modal) {
            this.elements.modal.style.display = 'none';
            document.body.style.overflow = 'auto';
            this.resetForm();
        }
    }
    
    resetForm() {
        this.elements.form?.reset();
        this.siteCounter = 0;
        this.elements.sitesContainer.innerHTML = '';
        this.clearFormErrors();
    }
    
    addSiteForm() {
        this.siteCounter++;
        const siteHTML = `
            <div class="site-form-group" data-site="${this.siteCounter}">
                <button type="button" class="remove-site-btn" onclick="this.parentElement.remove()">
                    <i class="material-icons">close</i>
                </button>
                <div class="form-grid">
                    <div class="form-group">
                        <label for="site-country-${this.siteCounter}">Pays</label>
                        <input type="text" id="site-country-${this.siteCounter}" name="site_country[]">
                    </div>
                    <div class="form-group">
                        <label for="site-city-${this.siteCounter}">Ville</label>
                        <input type="text" id="site-city-${this.siteCounter}" name="site_city[]">
                    </div>
                    <div class="form-group">
                        <label for="site-name-${this.siteCounter}">Nom du site</label>
                        <input type="text" id="site-name-${this.siteCounter}" name="site_name[]">
                    </div>
                    <div class="form-group">
                        <label for="site-gmp-${this.siteCounter}">
                            <input type="checkbox" id="site-gmp-${this.siteCounter}" name="site_gmp[]">
                            Certifié GMP
                        </label>
                    </div>
                </div>
            </div>
        `;
        this.elements.sitesContainer.insertAdjacentHTML('beforeend', siteHTML);
    }
    
    async submitForm() {
        console.log('Submitting form...');
        
        if (!this.validateForm()) {
            return;
        }
        
        const formData = new FormData(this.elements.form);
        
        // Prepare product data
        const productData = {
            name: formData.get('name'),
            active_ingredient: formData.get('active_ingredient'),
            dosage: formData.get('dosage'),
            form: formData.get('form'),
            therapeutic_area: formData.get('therapeutic_area'),
            status: formData.get('status')
        };
        
        // Prepare optional regulatory data
        const regulatoryData = {};
        if (formData.get('amm_number')) regulatoryData.amm_number = formData.get('amm_number');
        if (formData.get('approval_date')) regulatoryData.approval_date = formData.get('approval_date');
        if (formData.get('renewal_date')) regulatoryData.renewal_date = formData.get('renewal_date');
        if (formData.get('country_code')) regulatoryData.country_code = formData.get('country_code');
        
        // Prepare sites data
        const sitesData = [];
        const siteCountries = formData.getAll('site_country[]');
        const siteCities = formData.getAll('site_city[]');
        const siteNames = formData.getAll('site_name[]');
        const siteGMPs = formData.getAll('site_gmp[]');
        
        for (let i = 0; i < siteCountries.length; i++) {
            if (siteCountries[i] && siteCities[i] && siteNames[i]) {
                sitesData.push({
                    country: siteCountries[i],
                    city: siteCities[i],
                    site_name: siteNames[i],
                    gmp_certified: siteGMPs.includes('on')
                });
            }
        }
        
        // Disable submit button
        this.elements.saveBtn.disabled = true;
        this.elements.saveBtn.innerHTML = '<i class="material-icons">hourglass_empty</i> Enregistrement...';
        
        try {
            const response = await fetch('/client/products/api/products/', {
                method: 'POST',
                headers: {
                    'Content-Type': 'application/json',
                    'X-CSRFToken': this.getCSRFToken()
                },
                body: JSON.stringify({
                    product: productData,
                    regulatory: regulatoryData,
                    sites: sitesData
                })
            });
            
            if (response.ok) {
                const newProduct = await response.json();
                console.log('Product created successfully:', newProduct);
                
                this.showNotification('Produit créé avec succès !', 'success');
                this.hideModal();
                
                // Add new product to local array
                this.products.push(newProduct);
                
                // Re-render products list
                this.renderProducts(this.products);
                
                // Select the new product
                this.selectProduct(newProduct.id);
                
            } else {
                const error = await response.json();
                console.error('Error creating product:', error);
                this.showNotification('Erreur lors de la création du produit', 'error');
            }
        } catch (error) {
            console.error('Error submitting form:', error);
            this.showNotification('Erreur de connexion', 'error');
        } finally {
            this.elements.saveBtn.disabled = false;
            this.elements.saveBtn.innerHTML = '<i class="material-icons">save</i> Enregistrer';
        }
    }
    
    validateForm() {
        this.clearFormErrors();
        let isValid = true;
        
        // Required fields
        const requiredFields = ['name', 'active_ingredient', 'dosage', 'form', 'therapeutic_area', 'status'];
        
        requiredFields.forEach(fieldName => {
            const field = this.elements.form.querySelector(`[name="${fieldName}"]`);
            if (!field || !field.value.trim()) {
                this.showFieldError(field, 'Ce champ est requis');
                isValid = false;
            }
        });
        
        return isValid;
    }
    
    showFieldError(field, message) {
        const formGroup = field.closest('.form-group');
        formGroup.classList.add('error');
        
        const errorEl = document.createElement('div');
        errorEl.className = 'form-error';
        errorEl.textContent = message;
        formGroup.appendChild(errorEl);
    }
    
    clearFormErrors() {
        const errorElements = this.elements.form.querySelectorAll('.form-error');
        errorElements.forEach(el => el.remove());
        
        const errorGroups = this.elements.form.querySelectorAll('.form-group.error');
        errorGroups.forEach(group => group.classList.remove('error'));
    }
    
    getCSRFToken() {
        const token = document.querySelector('[name=csrfmiddlewaretoken]');
        return token ? token.value : '';
    }
    
    showNotification(message, type = 'info') {
        const notification = document.createElement('div');
        notification.className = `notification notification-${type}`;
        notification.textContent = message;
        
        // Add notification styles if not already present
        if (!document.querySelector('.notification-styles')) {
            const style = document.createElement('style');
            style.className = 'notification-styles';
            style.textContent = `
                .notification {
                    position: fixed;
                    top: 20px;
                    right: 20px;
                    padding: 12px 20px;
                    border-radius: 6px;
                    color: white;
                    font-weight: 500;
                    z-index: 9999;
                    animation: slideIn 0.3s ease;
                }
                .notification-success { background-color: #27ae60; }
                .notification-error { background-color: #e74c3c; }
                .notification-info { background-color: #3498db; }
                @keyframes slideIn {
                    from { transform: translateX(100%); opacity: 0; }
                    to { transform: translateX(0); opacity: 1; }
                }
            `;
            document.head.appendChild(style);
        }
        
        document.body.appendChild(notification);
        
        setTimeout(() => {
            notification.remove();
        }, 3000);
    }
    
    handleSearch(query) {
        if (!query.trim()) {
            this.renderProducts(this.products);
            return;
        }
        
        const filteredProducts = this.products.filter(product =>
            product.name.toLowerCase().includes(query.toLowerCase()) ||
            product.active_ingredient.toLowerCase().includes(query.toLowerCase())
        );
        
        this.renderProducts(filteredProducts);
    }
    
    formatDate(dateString) {
        if (!dateString) return 'N/A';
        try {
            return new Date(dateString).toLocaleDateString('fr-FR');
        } catch (error) {
            return dateString;
        }
    }
    
    getStatusLabel(status) {
        const labels = {
            'commercialise': 'Commercialisé',
            'developpement': 'En développement',
            'arrete': 'Arrêté',
            'soumis': 'Soumis',
            'en_cours': 'En cours',
            'approuve': 'Approuvé',
            'rejete': 'Rejeté'
        };
        return labels[status] || status;
    }

    getDocumentLabel(key) {
        const labels = {
            'ctd_dossier_complete': 'Dossier CTD complet',
            'gmp_certificate': 'Certificat GMP',
            'inspection_report': 'Rapport d\'inspection',
            'rcp_etiquetage': 'RCP et étiquetage'
        };
        return labels[key] || key;
    }
    // Sites management functions
async addSite() {
    if (!this.currentProductId) {
        this.showNotification('Aucun produit sélectionné', 'error');
        return;
    }
    
    const siteName = prompt('Nom du site:');
    const country = prompt('Pays:');
    const city = prompt('Ville:');
    
    if (siteName && country && city) {
        const gmpCertified = confirm('Site certifié GMP ?');
        
        try {
            const response = await fetch(`/client/products/api/products/${this.currentProductId}/sites/add/`, {
                method: 'POST',
                headers: {
                    'Content-Type': 'application/json',
                    'X-CSRFToken': this.getCSRFToken(),
                },
                body: JSON.stringify({
                    site_name: siteName,
                    country: country,
                    city: city,
                    gmp_certified: gmpCertified
                })
            });
            
            if (response.ok) {
                this.showNotification('Site ajouté avec succès', 'success');
                // Reload sites tab
                this.loadSitesTab();
            } else {
                this.showNotification('Erreur lors de l\'ajout', 'error');
            }
        } catch (error) {
            console.error('Error adding site:', error);
            this.showNotification('Erreur de connexion', 'error');
        }
    }
}

async viewSites() {
    if (!this.currentProductId) {
        this.showNotification('Aucun produit sélectionné', 'error');
        return;
    }
    
    try {
        const response = await fetch(`/client/products/api/products/${this.currentProductId}/sites/`);
        const sites = await response.json();
        
        if (sites.length === 0) {
            alert('Aucun site trouvé pour ce produit');
            return;
        }
        
        const sitesList = sites.map(site => 
            `• ${site.site_name || 'Nom non défini'} - ${site.city}, ${site.country}${site.gmp_certified ? ' (GMP Certifié)' : ''}`
        ).join('\n');
        
        alert(`Sites de production:\n\n${sitesList}`);
    } catch (error) {
        console.error('Error viewing sites:', error);
        this.showNotification('Erreur lors du chargement', 'error');
    }
}

async editSites() {
    if (!this.currentProductId) {
        this.showNotification('Aucun produit sélectionné', 'error');
        return;
    }
    
    try {
        const response = await fetch(`/client/products/api/products/${this.currentProductId}/sites/`);
        const sites = await response.json();
        
        if (sites.length === 0) {
            this.showNotification('Aucun site à modifier', 'info');
            return;
        }
        
        const siteOptions = sites.map((site, index) => 
            `${index + 1}. ${site.site_name || 'Nom non défini'} - ${site.city}, ${site.country}`
        ).join('\n');
        
        const selection = prompt(`Sélectionnez un site à modifier:\n${siteOptions}\n\nEntrez le numéro (1-${sites.length}):`);
        
        if (selection) {
            const siteIndex = parseInt(selection) - 1;
            if (siteIndex >= 0 && siteIndex < sites.length) {
                const site = sites[siteIndex];
                
                const newName = prompt('Nouveau nom du site:', site.site_name || '');
                const newCountry = prompt('Nouveau pays:', site.country || '');
                const newCity = prompt('Nouvelle ville:', site.city || '');
                
                if (newName && newCountry && newCity) {
                    const gmpCertified = confirm(`Site certifié GMP ? (actuellement: ${site.gmp_certified ? 'Oui' : 'Non'})`);
                    
                    const updateResponse = await fetch(`/client/products/api/sites/${site.id}/edit/`, {
                        method: 'PUT',
                        headers: {
                            'Content-Type': 'application/json',
                            'X-CSRFToken': this.getCSRFToken(),
                        },
                        body: JSON.stringify({
                            site_name: newName,
                            country: newCountry,
                            city: newCity,
                            gmp_certified: gmpCertified
                        })
                    });
                    
                    if (updateResponse.ok) {
                        this.showNotification('Site modifié avec succès', 'success');
                        this.loadSitesTab();
                    } else {
                        this.showNotification('Erreur lors de la modification', 'error');
                    }
                }
            } else {
                this.showNotification('Sélection invalide', 'error');
            }
        }
    } catch (error) {
        console.error('Error editing sites:', error);
        this.showNotification('Erreur lors du chargement', 'error');
    }
    }
    viewSourceDocument(productId) {
        if (!productId) {
            this.showNotification('Aucun produit sélectionné', 'error');
            return;
        }
        
        const documentUrl = `/client/products/api/products/${productId}/source-document/`;
        window.open(documentUrl, '_blank', 'width=1200,height=800,scrollbars=yes,resizable=yes');
    }
}

// View source document function

// Initialize
document.addEventListener('DOMContentLoaded', () => {
    if (window.location.pathname.includes('/client/products/')) {
        window.productsApp = new ProductsApp(); 
    }
});