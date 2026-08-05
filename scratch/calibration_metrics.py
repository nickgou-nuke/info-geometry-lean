import numpy as np

def brier_score(y_true_binary: np.ndarray, y_prob: np.ndarray) -> float:
    """Computes the Brier score for probability calibration."""
    valid = np.isfinite(y_true_binary) & np.isfinite(y_prob)
    if not np.any(valid):
        return 0.0
    return np.mean((y_prob[valid] - y_true_binary[valid])**2)

def expected_calibration_error(y_true: np.ndarray, y_prob: np.ndarray, n_bins: int = 10) -> float:
    """Computes the Expected Calibration Error (ECE)."""
    bins = np.linspace(0.0, 1.0, n_bins + 1)
    binids = np.digitize(y_prob, bins) - 1
    
    ece = 0.0
    total_samples = len(y_prob)
    
    for i in range(n_bins):
        mask = binids == i
        if np.any(mask):
            prob_pred = np.mean(y_prob[mask])
            prob_true = np.mean(y_true[mask])
            fraction = np.sum(mask) / total_samples
            ece += fraction * np.abs(prob_pred - prob_true)
            
    return ece

def background_metrics(B_true: np.ndarray, B_est: np.ndarray):
    """Computes the integrated squared error and max deviation for the background."""
    diff = B_est - B_true
    ise_b = np.sum(diff**2)
    delta_b_max = np.max(np.abs(diff))
    return ise_b, delta_b_max

def classification_metrics(y_true: np.ndarray, y_pred: np.ndarray):
    """Computes Recall, Precision, and FPR."""
    true_pos = np.sum(y_true & y_pred)
    false_pos = np.sum((~y_true) & y_pred)
    false_neg = np.sum(y_true & (~y_pred))
    
    recall = true_pos / (true_pos + false_neg) if (true_pos + false_neg) > 0 else 0.0
    precision = true_pos / (true_pos + false_pos) if (true_pos + false_pos) > 0 else 0.0
    
    pixels = y_true.size
    fpr = false_pos / pixels
    
    return recall, precision, fpr
