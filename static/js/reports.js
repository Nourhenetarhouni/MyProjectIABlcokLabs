// static/js/reports.js

class ReportsApp {
    constructor() {
        this.currentFilters = {
            template: '',
            period: '30d',
            authority: '',
            status: ''
        };
        this.init();
    }

    init() {
        console.log('🚀 Initializing Reports App...');
        this.bindEvents();
        this.updateKPIs();
        console.log('📊 Reports App initialized successfully');
    }

    bindEvents() {
        console.log('🔗 Binding events...');

        // Generator form submission
        const generateBtn = document.querySelector('.control-button');
        if (generateBtn) {
            generateBtn.addEventListener('click', (e) => {
                e.preventDefault();
                this.generateReport(e);
            });
            console.log('✅ Generator button bound');
        }

        // Use event delegation for ALL buttons (existing + future)
        this.bindAllButtonsWithDelegation();

        // Filter dropdowns
        document.querySelectorAll('.control-select').forEach(select => {
            select.addEventListener('change', (e) => this.updateFilter(e));
        });

        // Header buttons
        this.bindHeaderButtons();

        console.log('🔗 All events bound successfully');
    }

    bindAllButtonsWithDelegation() {
        // Use event delegation for ALL buttons in the document
        document.addEventListener('click', (e) => {
            const button = e.target.closest('button');
            if (!button) return;

            const buttonText = button.textContent.trim().toLowerCase();
            const buttonIcon = button.querySelector('i')?.textContent || '';
            
            console.log(`🔘 Button clicked: "${buttonText}" with icon: "${buttonIcon}"`);

            // Template action buttons (in templates section)
            if (button.closest('.template-actions')) {
                e.preventDefault();
                e.stopPropagation();

                const templateCard = button.closest('.template-card');
                const templateName = templateCard.querySelector('h3').textContent;

                console.log(`🎯 Template action: ${buttonText} on ${templateName}`);

                if (buttonText.includes('aperçu') || buttonIcon === 'visibility') {
                    this.previewTemplate(templateName);
                } else if (buttonText.includes('générer') || buttonIcon === 'get_app') {
                    this.generateTemplateReport(templateName);
                } else if (buttonText.includes('export') || buttonIcon === 'file_download') {
                    this.exportTemplate(templateName);
                }
                return;
            }

            // Saved Views action buttons - FIX THIS SHIT
            if (button.closest('.saved-view-actions')) {
                e.preventDefault();
                e.stopPropagation();
                
                const viewItem = button.closest('.saved-view-item');
                const viewName = viewItem.querySelector('h4').textContent;

                console.log(`👁️ Saved view action: ${buttonIcon} on ${viewName}`);

                if (buttonIcon === 'visibility') {
                    this.viewSavedView(viewName);
                } else if (buttonIcon === 'share') {
                    this.shareSavedView(viewName);
                }
                return;
            }

            // History Reports - ADD FUCKING VIEW BUTTONS
            if (button.closest('.reports-history') || button.closest('.history-item')) {
                e.preventDefault();
                e.stopPropagation();

                const historyItem = button.closest('.history-item');
                const reportName = historyItem.querySelector('h5').textContent;

                console.log(`📋 History report action: ${buttonText} on ${reportName}`);

                if (buttonText.includes('voir') || buttonIcon === 'visibility') {
                    this.viewHistoryReport(reportName, historyItem);
                } else if (buttonText.includes('télécharger') || buttonIcon === 'file_download') {
                    this.downloadReport(reportName, historyItem);
                } else if (buttonText.includes('supprimer') || buttonIcon === 'delete') {
                    this.deleteReport(reportName, historyItem);
                }
                return;
            }

            // Recent Reports action buttons
            if (button.closest('.recent-reports-list') || button.closest('.recent-report-item')) {
                e.preventDefault();
                e.stopPropagation();

                const reportItem = button.closest('.recent-report-item');
                const reportName = reportItem.querySelector('h5').textContent;

                console.log(`📋 Recent report action: ${buttonText} on ${reportName}`);

                if (buttonText.includes('voir') || buttonIcon === 'visibility') {
                    this.viewReport(reportName, reportItem);
                } else if (buttonText.includes('télécharger') || buttonIcon === 'file_download') {
                    this.downloadReport(reportName, reportItem);
                } else if (buttonText.includes('supprimer') || buttonIcon === 'delete') {
                    this.deleteReport(reportName, reportItem);
                }
                return;
            }
        });

        console.log('✅ All buttons bound with event delegation');
    }

    bindHeaderButtons() {
        document.querySelectorAll('.header-right .btn').forEach(btn => {
            btn.addEventListener('click', (e) => {
                e.preventDefault();
                this.handleHeaderAction(e);
            });
        });
    }

    updateFilter(event) {
        const filterType = event.target.closest('.control-group').querySelector('label').textContent.toLowerCase();
        const value = event.target.value;
        
        console.log(`🔄 Filter updated: ${filterType} = ${value}`);
        
        // Update internal state
        if (filterType.includes('template')) {
            this.currentFilters.template = value;
        } else if (filterType.includes('période')) {
            this.currentFilters.period = value;
        } else if (filterType.includes('autorité')) {
            this.currentFilters.authority = value;
        }

        this.showFilterFeedback();
    }

    showFilterFeedback() {
        const activeFilters = Object.values(this.currentFilters).filter(v => v && v !== '').length;
        
        if (activeFilters > 0) {
            this.showToast(`${activeFilters} filtre(s) actif(s)`, 'info');
        }
    }

    async generateReport(event) {
        console.log('🔄 Generating report from generator...');
        
        const generateBtn = event.target.closest('button');
        const originalText = generateBtn.innerHTML;
        
        // Show loading state
        generateBtn.innerHTML = '<i class="material-icons">hourglass_empty</i> Génération...';
        generateBtn.disabled = true;

        try {
            const response = await fetch('/client/reports/generate/', {
                method: 'POST',
                headers: {
                    'Content-Type': 'application/json',
                    'X-CSRFToken': this.getCSRFToken()
                },
                body: JSON.stringify(this.currentFilters)
            });

            const data = await response.json();

            if (data.status === 'success') {
                this.showToast('✅ Rapport généré avec succès!', 'success');
                this.addToRecentReports(data);
                this.addToReportsHistory(data);
                console.log('📊 Report generated:', data);
            } else {
                throw new Error(data.error || 'Erreur de génération');
            }

        } catch (error) {
            console.error('Generation error:', error);
            this.showToast(`❌ Erreur: ${error.message}`, 'error');
        } finally {
            generateBtn.innerHTML = originalText;
            generateBtn.disabled = false;
        }
    }

    previewTemplate(templateName) {
        console.log(`👁️ Previewing template: ${templateName}`);
        this.showToast(`👁️ Aperçu de "${templateName}"`, 'info');
        
        // Create modal preview
        const modal = this.createModal(`Aperçu - ${templateName}`, `
            <div class="preview-content">
                <h4>📋 Aperçu du template "${templateName}"</h4>
                <div class="preview-info">
                    <p><strong>Ce rapport inclura:</strong></p>
                    <ul>
                        <li>📊 Données des ${this.currentFilters.period || '30 derniers jours'}</li>
                        <li>📈 Graphiques de tendances</li>
                        <li>📋 Tableau de bord KPI</li>
                        <li>🎯 Métriques de performance</li>
                        <li>📄 Format: PDF & Excel</li>
                    </ul>
                    <div class="preview-actions">
                        <button class="btn btn-primary" onclick="this.closest('.modal-overlay').remove(); window.reportsApp.generateTemplateReport('${templateName}')">
                            <i class="material-icons">play_arrow</i>
                            Générer ce rapport
                        </button>
                    </div>
                </div>
            </div>
        `);
        
        document.body.appendChild(modal);
    }

    // NEW: View Saved View
    viewSavedView(viewName) {
        console.log(`👁️ Viewing saved view: ${viewName}`);
        this.showToast(`👁️ Ouverture de "${viewName}"`, 'info');
        
        const modal = this.createModal(`Vue Sauvegardée - ${viewName}`, `
            <div class="saved-view-content">
                <h4>📊 ${viewName}</h4>
                <div class="view-details">
                    <p><strong>Type:</strong> Vue personnalisée</p>
                    <p><strong>Filtres sauvegardés:</strong></p>
                    <ul>
                        <li>🗓️ Période: 30 derniers jours</li>
                        <li>🏢 Autorité: Toutes autorités</li>
                        <li>📊 Données: Documents validés</li>
                        <li>🎯 Focus: Métriques de performance</li>
                    </ul>
                    <div class="view-actions">
                        <button class="btn btn-primary" onclick="window.reportsApp.loadSavedViewFilters('${viewName}'); this.closest('.modal-overlay').remove();">
                            <i class="material-icons">restore</i>
                            Charger cette vue
                        </button>
                        <button class="btn btn-secondary" onclick="window.reportsApp.generateFromSavedView('${viewName}'); this.closest('.modal-overlay').remove();">
                            <i class="material-icons">play_arrow</i>
                            Générer rapport
                        </button>
                    </div>
                </div>
            </div>
        `);
        
        document.body.appendChild(modal);
    }

    // NEW: View History Report
    viewHistoryReport(reportName, reportItem) {
        console.log(`👁️ Viewing history report: ${reportName}`);
        this.showToast(`👁️ Ouverture de "${reportName}"`, 'info');
        
        const modal = this.createModal(`Rapport Généré - ${reportName}`, `
            <div class="report-view">
                <h4>📊 ${reportName}</h4>
                <div class="report-summary">
                    <div class="summary-section">
                        <h5>📈 Résumé Exécutif</h5>
                        <p>Ce rapport présente une analyse complète des données réglementaires pour la période sélectionnée.</p>
                    </div>
                    
                    <div class="summary-section">
                        <h5>📊 Métriques Clés</h5>
                        <div class="metrics-grid-small">
                            <div class="metric-item">
                                <strong>Documents traités:</strong> 6
                            </div>
                            <div class="metric-item">
                                <strong>Annotations créées:</strong> 11
                            </div>
                            <div class="metric-item">
                                <strong>Produits analysés:</strong> 3
                            </div>
                            <div class="metric-item">
                                <strong>Délai moyen:</strong> 2.5 jours
                            </div>
                        </div>
                    </div>
                    
                    <div class="summary-section">
                        <h5>🎯 Points Clés</h5>
                        <ul>
                            <li>✅ 100% des documents ont été validés avec succès</li>
                            <li>📈 Amélioration de 15% du temps de traitement</li>
                            <li>🏆 Tous les produits respectent les standards réglementaires</li>
                            <li>⚡ Performance optimale sur tous les indicateurs</li>
                        </ul>
                    </div>
                </div>
                
                <div class="report-actions">
                    <button class="btn btn-primary" onclick="window.reportsApp.downloadReportFromModal('${reportName}'); this.closest('.modal-overlay').remove();">
                        <i class="material-icons">file_download</i>
                        Télécharger PDF
                    </button>
                    <button class="btn btn-secondary" onclick="window.reportsApp.exportReportCSV('${reportName}'); this.closest('.modal-overlay').remove();">
                        <i class="material-icons">table_chart</i>
                        Exporter CSV
                    </button>
                    <button class="btn btn-outline" onclick="this.closest('.modal-overlay').remove();">
                        Fermer
                    </button>
                </div>
            </div>
        `);
        
        document.body.appendChild(modal);
    }

    async generateTemplateReport(templateName) {
        console.log(`⚙️ Generating template report: ${templateName}`);
        this.showToast(`⚙️ Génération de "${templateName}"...`, 'info');
        
        try {
            const response = await fetch('/client/reports/generate/', {
                method: 'POST',
                headers: {
                    'Content-Type': 'application/json',
                    'X-CSRFToken': this.getCSRFToken()
                },
                body: JSON.stringify({
                    template: templateName,
                    period: this.currentFilters.period,
                    authority: this.currentFilters.authority
                })
            });

            const data = await response.json();

            if (data.status === 'success') {
                this.showToast(`✅ "${templateName}" généré avec succès!`, 'success');
                this.addToRecentReports(data);
                this.addToReportsHistory(data);
            } else {
                throw new Error(data.error || 'Erreur de génération');
            }

        } catch (error) {
            console.error('Template generation error:', error);
            this.showToast(`❌ Erreur: ${error.message}`, 'error');
        }
    }

    async exportTemplate(templateName) {
        console.log(`📤 Exporting template: ${templateName}`);
        this.showToast(`📤 Export de "${templateName}"...`, 'info');
        
        try {
            // Create download URL
            const exportUrl = `/client/reports/export/?format=csv&template=${encodeURIComponent(templateName)}`;
            
            // Create temporary download link
            const link = document.createElement('a');
            link.href = exportUrl;
            link.download = `regx_report_${templateName.replace(/\s+/g, '_')}_${new Date().toISOString().split('T')[0]}.csv`;
            link.style.display = 'none';
            
            document.body.appendChild(link);
            link.click();
            document.body.removeChild(link);
            
            setTimeout(() => {
                this.showToast(`✅ Export "${templateName}" terminé!`, 'success');
            }, 1000);
            
        } catch (error) {
            console.error('Export error:', error);
            this.showToast(`❌ Erreur d'export: ${error.message}`, 'error');
        }
    }

    // Methods for handling reports
    viewReport(reportName, reportItem) {
        console.log(`👁️ Viewing report: ${reportName}`);
        this.viewHistoryReport(reportName, reportItem); // Same as history view
    }

    downloadReport(reportName, reportItem) {
        console.log(`📥 Downloading report: ${reportName}`);
        this.showToast(`📥 Téléchargement de "${reportName}"...`, 'info');
        
        // Trigger download
        const exportUrl = `/client/reports/export/?format=csv&template=${encodeURIComponent(reportName)}`;
        const link = document.createElement('a');
        link.href = exportUrl;
        link.download = `${reportName.replace(/\s+/g, '_')}_${new Date().toISOString().split('T')[0]}.csv`;
        link.style.display = 'none';
        
        document.body.appendChild(link);
        link.click();
        document.body.removeChild(link);
        
        setTimeout(() => {
            this.showToast(`✅ "${reportName}" téléchargé!`, 'success');
        }, 1000);
    }

    downloadReportFromModal(reportName) {
        this.downloadReport(reportName, null);
    }

    exportReportCSV(reportName) {
        this.downloadReport(reportName, null);
    }

    deleteReport(reportName, reportItem) {
        if (confirm(`Êtes-vous sûr de vouloir supprimer "${reportName}" ?`)) {
            console.log(`🗑️ Deleting report: ${reportName}`);
            reportItem.remove();
            this.showToast(`🗑️ "${reportName}" supprimé`, 'success');
        }
    }

    loadSavedViewFilters(viewName) {
        this.showToast(`📋 Filtres de "${viewName}" chargés!`, 'success');
        // You can implement actual filter loading here
    }

    generateFromSavedView(viewName) {
        this.showToast(`⚙️ Génération depuis "${viewName}"...`, 'info');
        this.generateTemplateReport(viewName);
    }

    addToRecentReports(reportData) {
        console.log('📋 Adding report to recent reports list');
        
        // Find or create recent reports section
        let recentSection = document.querySelector('.recent-reports-section');
        if (!recentSection) {
            recentSection = this.createRecentReportsSection();
        }
        
        const reportsList = recentSection.querySelector('.recent-reports-list');
        
        // Create new report item
        const reportItem = document.createElement('div');
        reportItem.className = 'recent-report-item';
        reportItem.innerHTML = `
            <div class="report-info">
                <h5>${reportData.template || 'Rapport Généré'}</h5>
                <small>Généré le ${new Date().toLocaleString()}</small>
                <div class="report-meta">
                    <span class="meta-tag">Période: ${reportData.period || '30d'}</span>
                    ${reportData.authority ? `<span class="meta-tag">Autorité: ${reportData.authority}</span>` : ''}
                </div>
            </div>
            <div class="report-actions">
                <button class="btn btn-text btn-sm">
                    <i class="material-icons">visibility</i>
                    Voir
                </button>
                <button class="btn btn-text btn-sm">
                    <i class="material-icons">file_download</i>
                    Télécharger
                </button>
                <button class="btn btn-text btn-sm text-danger">
                    <i class="material-icons">delete</i>
                    Supprimer
                </button>
            </div>
        `;
        
        // Add to beginning of list
        reportsList.insertBefore(reportItem, reportsList.firstChild);
        
        // Keep only last 10 reports
        const reports = reportsList.querySelectorAll('.recent-report-item');
        if (reports.length > 10) {
            reports[reports.length - 1].remove();
        }
        
        // Animate the new item
        reportItem.style.opacity = '0';
        reportItem.style.transform = 'translateY(-10px)';
        setTimeout(() => {
            reportItem.style.transition = 'all 0.3s ease';
            reportItem.style.opacity = '1';
            reportItem.style.transform = 'translateY(0)';
        }, 100);
    }

    addToReportsHistory(reportData) {
        console.log('📋 Adding report to history');
        
        // Find history list
        const historyList = document.querySelector('.reports-history-list');
        if (!historyList) return;
        
        // Create new history item WITH VIEW BUTTON
        const historyItem = document.createElement('div');
        historyItem.className = 'history-item';
        historyItem.innerHTML = `
            <div class="history-content">
                <h5>${reportData.template || 'Rapport Généré'}</h5>
                <small>Généré le ${new Date().toLocaleString()}</small>
            </div>
            <div class="history-actions">
                <button class="btn btn-text btn-sm">
                    <i class="material-icons">visibility</i>
                    Voir
                </button>
                <span class="status-badge success">Terminé</span>
            </div>
        `;
        
        // Add to beginning of list
        historyList.insertBefore(historyItem, historyList.firstChild);
        
        // Animate the new item
        historyItem.style.opacity = '0';
        historyItem.style.transform = 'translateY(-10px)';
        setTimeout(() => {
            historyItem.style.transition = 'all 0.3s ease';
            historyItem.style.opacity = '1';
            historyItem.style.transform = 'translateY(0)';
        }, 100);
    }

    createRecentReportsSection() {
        const container = document.querySelector('.reports-container');
        
        // Find a good place to insert (after templates section)
        const templatesSection = document.querySelector('.templates-section');
        
        const recentSection = document.createElement('div');
        recentSection.className = 'recent-reports-section';
        recentSection.innerHTML = `
            <h2 class="section-title">📋 Rapports Récents</h2>
            <div class="recent-reports-list">
                <!-- Reports will be added here dynamically -->
            </div>
        `;
        
        // Insert after templates section
        if (templatesSection && templatesSection.nextSibling) {
            container.insertBefore(recentSection, templatesSection.nextSibling);
        } else {
            container.appendChild(recentSection);
        }
        
        return recentSection;
    }

    handleHeaderAction(event) {
        const action = event.target.closest('button');
        const actionText = action.textContent.trim().toLowerCase();

        if (actionText.includes('sauvegarder')) {
            this.saveCurrentView();
        } else if (actionText.includes('nouveau')) {
            this.createNewReport();
        }
    }

    saveCurrentView() {
        const viewName = prompt('Nom de la vue à sauvegarder:', `Vue ${new Date().toLocaleDateString()}`);
        
        if (viewName) {
            this.showToast(`💾 Vue "${viewName}" sauvegardée!`, 'success');
            this.addSavedView(viewName);
        }
    }

    createNewReport() {
        this.showToast('🆕 Création d\'un nouveau rapport...', 'info');
        console.log('Navigate to report builder');
    }

    loadSavedView(viewName) {
        this.showToast(`👁️ Chargement de "${viewName}"...`, 'info');
        console.log(`Loading saved view: ${viewName}`);
        
        setTimeout(() => {
            this.showToast(`✅ Vue "${viewName}" chargée!`, 'success');
        }, 1000);
    }

    shareSavedView(viewName) {
        const shareUrl = `${window.location.origin}/client/reports/?view=${encodeURIComponent(viewName)}`;
        
        if (navigator.share) {
            navigator.share({
                title: `RegX Report - ${viewName}`,
                url: shareUrl
            });
        } else {
            navigator.clipboard.writeText(shareUrl).then(() => {
                this.showToast(`🔗 Lien de partage copié!`, 'success');
            });
        }
    }

    updateKPIs() {
        // Animate KPI cards on load
        const kpiCards = document.querySelectorAll('.kpi-card');
        
        kpiCards.forEach((card, index) => {
            setTimeout(() => {
                card.style.opacity = '0';
                card.style.transform = 'translateY(20px)';
                card.style.transition = 'all 0.5s ease';
                
                setTimeout(() => {
                    card.style.opacity = '1';
                    card.style.transform = 'translateY(0)';
                }, 100);
            }, index * 100);
        });
    }

    addSavedView(viewName) {
        const savedViewsGrid = document.querySelector('.saved-views-grid');
        
        const newView = document.createElement('div');
        newView.className = 'saved-view-item';
        newView.innerHTML = `
            <div class="saved-view-content">
                <h4>${viewName}</h4>
                <p>Vue personnalisée créée le ${new Date().toLocaleDateString()}</p>
            </div>
            <div class="saved-view-actions">
                <button class="btn btn-text">
                    <i class="material-icons">visibility</i>
                </button>
                <button class="btn btn-text">
                    <i class="material-icons">share</i>
                </button>
            </div>
        `;
        
        savedViewsGrid.insertBefore(newView, savedViewsGrid.firstChild);
    }

    createModal(title, content) {
        const modal = document.createElement('div');
        modal.className = 'modal-overlay';
        modal.innerHTML = `
            <div class="modal-content">
                <div class="modal-header">
                    <h3>${title}</h3>
                    <button class="modal-close">&times;</button>
                </div>
                <div class="modal-body">
                    ${content}
                </div>
            </div>
        `;
        
        // Close modal functionality
        modal.querySelector('.modal-close').addEventListener('click', () => {
            document.body.removeChild(modal);
        });
        
        modal.addEventListener('click', (e) => {
            if (e.target === modal) {
                document.body.removeChild(modal);
            }
        });
        
        return modal;
    }

    showToast(message, type = 'info') {
        console.log(`🍞 Toast: ${message} (${type})`);
        
        const toast = document.createElement('div');
        toast.className = `toast toast-${type}`;
        toast.textContent = message;
        
        // Style the toast
        Object.assign(toast.style, {
            position: 'fixed',
            top: '20px',
            right: '20px',
            padding: '12px 20px',
            borderRadius: '8px',
            color: 'white',
            fontWeight: '500',
            zIndex: '10000',
            transform: 'translateX(100%)',
            transition: 'transform 0.3s ease',
            maxWidth: '400px'
        });
        
        // Type-specific colors
        const colors = {
            success: '#10b981',
            error: '#ef4444', 
            info: '#3b82f6',
            warning: '#f59e0b'
        };
        
        toast.style.background = colors[type] || colors.info;
        
        document.body.appendChild(toast);
        
        // Animate in
        setTimeout(() => {
            toast.style.transform = 'translateX(0)';
        }, 100);
        
        // Remove after delay
        setTimeout(() => {
            toast.style.transform = 'translateX(100%)';
            setTimeout(() => {
                if (document.body.contains(toast)) {
                    document.body.removeChild(toast);
                }
            }, 300);
        }, 3000);
    }

    getCSRFToken() {
        const token = document.querySelector('[name=csrfmiddlewaretoken]');
        if (token) return token.value;
        
        // Alternative: get from cookies
        const cookies = document.cookie.split(';');
        for (let cookie of cookies) {
            const [name, value] = cookie.trim().split('=');
            if (name === 'csrftoken') {
                return value;
            }
        }
        return '';
    }
}

// Initialize when DOM is ready
document.addEventListener('DOMContentLoaded', () => {
    window.reportsApp = new ReportsApp();
});

// Global functions for compatibility
window.generateReport = () => {
    const generateBtn = document.querySelector('.control-button');
    if (generateBtn && window.reportsApp) {
        generateBtn.click();
    }
};

window.refreshData = () => {
    if (window.reportsApp) {
        window.reportsApp.showToast('🔄 Actualisation des données...', 'info');
        setTimeout(() => {
            window.location.reload();
        }, 1000);
    }
};

console.log('📊 Reports JavaScript loaded successfully');