// static/rawdocs/js/rlhf_annotation.js

// Enhanced AI annotation with RLHF learning
function annotateWithGroq() {
    const btn = document.getElementById('groq-annotate-btn');
    const loading = document.getElementById('ai-loading');
    const validateBtn = document.getElementById('validate-page-btn');

    if (!btn || !loading) return;

    btn.style.display = 'none';
    loading.style.display = 'flex';

    const pageId = document.getElementById('text-content')?.dataset?.pageId;
    if (!pageId) {
        showErrorMessage('Page ID non trouvée');
        return;
    }

    fetch(`/annotation/groq/${pageId}/`, {
        method: 'POST',
        headers: {
            'X-CSRFToken': getCookie('csrftoken'),
            'Content-Type': 'application/json'
        }
    })
    .then(handleResponse)
    .then(data => {
        if (data.success) {
            showSuccessMessage(`🎉 ${data.annotations_created} annotations créées avec IA améliorée!`);

            if (validateBtn) {
                validateBtn.disabled = false;
                validateBtn.innerHTML = '<i class="fas fa-graduation-cap"></i> Valider la Page';
            }

            setTimeout(() => location.reload(), 1500);
        } else {
            throw new Error(data.error || 'Erreur inconnue lors de l\'annotation');
        }
    })
    .catch(error => {
        console.error('Annotation Error:', error);
        showErrorMessage(`Erreur annotation: ${error.message}`);
    })
    .finally(() => {
        btn.style.display = 'flex';
        loading.style.display = 'none';
    });
}

// Enhanced validate page function with better error handling
function validatePage() {
    const btn = document.getElementById('validate-page-btn');
    const learningProgress = document.getElementById('learning-progress');
    const pageId = document.getElementById('text-content')?.dataset?.pageId;

    if (!btn || !pageId) {
        showErrorMessage('Éléments manquants pour la validation');
        return;
    }

    if (!confirm('Valider cette page ? L\'IA va apprendre de vos corrections.')) {
        return;
    }

    btn.disabled = true;
    btn.innerHTML = '<i class="fas fa-spinner fa-spin"></i> Validation en cours...';

    if (learningProgress) {
        learningProgress.style.display = 'flex';
    }

    fetch(`/annotation/validate-page/${pageId}/`, {
        method: 'POST',
        headers: {
            'X-CSRFToken': getCookie('csrftoken'),
            'Content-Type': 'application/json'
        }
    })
    .then(handleResponse)
    .then(data => {
        if (data.success) {
            showValidationSuccess(data.message, data.feedback_score, data.corrections_summary);
            btn.innerHTML = '<i class="fas fa-check-circle"></i> Page Validée 🎓';
            btn.classList.add('validated');
            showLearningWidget(data);
            updatePageSelector();
        } else {
            throw new Error(data.error || 'Échec de la validation');
        }
    })
    .catch(error => {
        console.error('Validation Error:', error);
        showErrorMessage(`Erreur validation: ${error.message}`);
        btn.disabled = false;
        btn.innerHTML = '<i class="fas fa-graduation-cap"></i> Valider la Page';
    })
    .finally(() => {
        if (learningProgress) {
            learningProgress.style.display = 'none';
        }
    });
}

// Helper function to handle fetch responses
function handleResponse(response) {
    if (!response.ok) {
        return response.json().then(err => {
            throw new Error(err.error || `HTTP error! status: ${response.status}`);
        });
    }
    return response.json();
}

// Enhanced validation success display
function showValidationSuccess(message, feedbackScore, corrections = {}) {
    // Conteneurs plus spécifiques à votre structure HTML
    let container = document.querySelector('.text-content-card') ||
                   document.querySelector('.annotations-list') ||
                   document.querySelector('.page-navigation') ||
                   document.body;

    if (!container) {
        console.error("Aucun conteneur trouvé pour afficher le message de validation");
        return;
    }

    // Calcul des métriques avec valeurs par défaut
    const metrics = {
        kept_correct: corrections.kept_correct?.length || 0,
        false_positives: corrections.false_positives?.length || 0,
        false_negatives: corrections.false_negatives?.length || 0,
        wrong_classifications: corrections.wrong_classifications?.length || 0
    };

    const totalExpected = Object.values(metrics).reduce((a, b) => a + b, 0);
    const scorePercent = (feedbackScore * 100).toFixed(0);

    const successDiv = document.createElement('div');
    successDiv.className = 'validation-success';
    successDiv.innerHTML = `
        <i class="fas fa-graduation-cap"></i>
        <div>
            <strong>${message}</strong>
            <div class="validation-details">
                <div class="feedback-breakdown">
                    ${createMetricRow('✅', 'Correctes (conservées)', metrics.kept_correct)}
                    ${createMetricRow('❌', 'Incorrectes (supprimées)', metrics.false_positives)}
                    ${createMetricRow('➕', 'Manquées (ajoutées)', metrics.false_negatives)}
                    ${metrics.wrong_classifications > 0 ? 
                      createMetricRow('🔄', 'Mauvais type', metrics.wrong_classifications) : ''}
                    ${createMetricRow('📊', 'Total attendu', totalExpected, 'total')}
                    ${createMetricRow('🎯', 'Score réel', `${scorePercent}%`, 'score')}
                </div>
            </div>
        </div>
    `;

    // Style du message de succès
    successDiv.style.cssText = `
        background: linear-gradient(45deg, #10b981, #059669);
        color: white;
        padding: 1rem 1.5rem;
        border-radius: 8px;
        box-shadow: 0 4px 15px rgba(0,0,0,0.1);
        margin-bottom: 1rem;
        display: flex;
        align-items: center;
        gap: 1rem;
    `;

    // Méthode d'insertion plus robuste
    try {
        if (container === document.body) {
            successDiv.style.position = 'fixed';
            successDiv.style.top = '20px';
            successDiv.style.right = '20px';
            successDiv.style.zIndex = '1000';
            container.appendChild(successDiv);
        } else {
            // Insertion en haut du conteneur si possible
            if (container.firstChild) {
                container.insertBefore(successDiv, container.firstChild);
            } else {
                container.appendChild(successDiv);
            }
        }
    } catch (e) {
        console.error("Erreur d'insertion du message:", e);
        // Fallback simple
        document.body.appendChild(successDiv);
    }

    setTimeout(() => {
        successDiv.style.opacity = '0';
        setTimeout(() => successDiv.remove(), 500);
    }, 5000);
}

function createMetricRow(icon, text, value, extraClass = '') {
    return `
        <div class="metric-row ${extraClass}">
            <span class="metric-icon">${icon}</span>
            <span class="metric-text">${text}: ${value}</span>
        </div>
    `;
}

// Learning widget with performance indicators
function showLearningWidget(data) {
    let widget = document.getElementById('learning-widget') || createLearningWidget();

    fetch('/learning/dashboard/')
        .then(handleResponse)
        .then(learningData => {
            const avgScore = (learningData.average_feedback_score * 100).toFixed(0);
            const {performanceLevel, performanceIcon} = getPerformanceLevel(avgScore);

            widget.innerHTML = `
                <h4><i class="fas fa-chart-line"></i> Progrès d'Apprentissage IA</h4>
                <div class="learning-metrics">
                    ${createLearningMetric('Score Réel', `${avgScore}%`, `${performanceIcon} ${performanceLevel}`)}
                    ${createLearningMetric('Validations', learningData.total_feedbacks)}
                    ${createLearningMetric('Amélioration', '📈 Active')}
                </div>
                <div class="learning-explanation">
                    <small><i class="fas fa-info-circle"></i> Score basé sur annotations correctes, erreurs et manqués</small>
                </div>
            `;
            widget.style.display = 'block';
        })
        .catch(error => {
            console.error('Learning Dashboard Error:', error);
            widget.innerHTML = `
                <h4><i class="fas fa-chart-line"></i> Progrès d'Apprentissage</h4>
                <div class="learning-error">
                    <i class="fas fa-exclamation-triangle"></i> Données non disponibles
                </div>
            `;
        });
}

function createLearningWidget() {
    const widget = document.createElement('section');
    widget.id = 'learning-widget';
    widget.className = 'learning-dashboard-widget';
    document.querySelector('.text-content-card')?.appendChild(widget);
    return widget;
}

function createLearningMetric(label, value, extra = '') {
    return `
        <div class="metric">
            <span class="metric-label">${label}:</span>
            <span class="metric-value">${value}</span>
            ${extra ? `<span class="performance-indicator">${extra}</span>` : ''}
        </div>
    `;
}

function getPerformanceLevel(score) {
    score = parseInt(score);
    if (score >= 90) return {performanceLevel: 'Excellent', performanceIcon: '🏆'};
    if (score >= 75) return {performanceLevel: 'Bon', performanceIcon: '👍'};
    if (score >= 50) return {performanceLevel: 'Apprentissage', performanceIcon: '🎓'};
    return {performanceLevel: 'Nécessite entrainement', performanceIcon: '📚'};
}

// Update page selector UI
function updatePageSelector() {
    const pageSelect = document.getElementById('page-select');
    const currentOption = pageSelect?.querySelector('option:checked');

    if (currentOption && !currentOption.textContent.includes('🎓')) {
        currentOption.textContent = currentOption.textContent.replace('✅', '🎓');
    }
}

// UI Helpers
function showSuccessMessage(message) {
    showAlert(message, 'success', '#10b981');
}

function showErrorMessage(message) {
    showAlert(message, 'error', '#ef4444');
}

function showAlert(message, type, color) {
    const alert = document.createElement('div');
    alert.className = `alert alert-${type}`;
    alert.style.cssText = `
        position: fixed;
        top: 20px;
        right: 20px;
        background: linear-gradient(45deg, ${color}, ${darkenColor(color)});
        color: white;
        padding: 1rem 1.5rem;
        border-radius: 8px;
        box-shadow: 0 4px 15px rgba(0,0,0,0.1);
        z-index: 1000;
        font-weight: 600;
        display: flex;
        align-items: center;
        gap: 0.5rem;
    `;
    alert.innerHTML = `
        <i class="fas fa-${type === 'success' ? 'check-circle' : 'exclamation-circle'}"></i>
        ${message}
    `;

    document.body.appendChild(alert);
    setTimeout(() => alert.remove(), 4000);
}

function darkenColor(hex, amount = 0.2) {
    // Simple color darkening for the gradient
    return hex; // Implement proper color manipulation if needed
}

// Initialize on page load
document.addEventListener('DOMContentLoaded', function() {
    // Mark validated pages
    const validateBtn = document.getElementById('validate-page-btn');
    if (validateBtn?.textContent?.includes('Validée')) {
        showLearningWidget({});
    }

    // Add indicators to AI-generated annotations
    document.querySelectorAll('.annotation-item').forEach(annotation => {
        if (annotation.querySelector('.annotation-reasoning')?.textContent?.includes('RLHF')) {
            annotation.classList.add('ai-generated');
            const indicator = document.createElement('div');
            indicator.className = 'rlhf-indicator';
            indicator.innerHTML = '<i class="fas fa-brain"></i> IA Apprenante';
            annotation.appendChild(indicator);
        }
    });
});

// CSRF token helper
function getCookie(name) {
    const value = `; ${document.cookie}`;
    const parts = value.split(`; ${name}=`);
    if (parts.length === 2) return parts.pop().split(';').shift();
}