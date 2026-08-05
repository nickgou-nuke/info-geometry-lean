import numpy as np
from dataclasses import dataclass
from typing import Tuple, Dict, Any, Optional, Union

@dataclass(frozen=True)
class CalibratedFrame:
    electrons: np.ndarray
    invalid_mask: np.ndarray
    saturation_mask: np.ndarray
    gain_e_per_adu: Union[np.ndarray, float]
    pedestal_adu: Union[np.ndarray, float]
    metadata: dict

class SyntheticFITSGenerator:
    def __init__(self, shape: Tuple[int, int] = (100, 100), sigma_read: float = 5.0):
        self.shape = shape
        self.sigma_read = sigma_read
        
    def generate_background(self, base_level: float = 100.0) -> np.ndarray:
        """Generates B* latent background with spatial variations."""
        P_p = np.ones(self.shape)  # stable spatial pattern
        I_t = base_level           # global illumination
        d_pt = np.zeros(self.shape)  # pixel drift
        F_pt = np.zeros(self.shape)  # smooth scene component
        return P_p * I_t + d_pt + F_pt

    def generate_clean_frame(self, B_star: np.ndarray) -> np.ndarray:
        """Generates measured clean frame using Poisson-Gaussian law."""
        poisson_shot = np.random.poisson(B_star).astype(np.float64)
        read_noise = np.random.normal(0, self.sigma_read, size=self.shape)
        return poisson_shot + read_noise

    def inject_cosmic_ray(self, X: np.ndarray, Q: float, L: float, phi: float, w: float, x0: int, y0: int) -> np.ndarray:
        """Injects a cosmic ray track."""
        X_out = X.copy()
        y_indices, x_indices = np.indices(self.shape)
        
        # Translate to origin
        dx = x_indices - x0
        dy = y_indices - y0
        
        # Rotate coordinates
        d_par = dx * np.cos(phi) + dy * np.sin(phi)
        d_perp = -dx * np.sin(phi) + dy * np.cos(phi)
        
        # Compute track profile
        C_tilde = np.exp(- (d_perp**2) / (2 * w**2)) * (np.abs(d_par) <= L/2)
        
        # Normalize and scale by Q
        C_sum = np.sum(C_tilde)
        if C_sum > 0:
            C = Q * (C_tilde / C_sum)
            X_out += C
            
        return X_out

    def inject_dropout(self, X: np.ndarray, H: float, mask: np.ndarray) -> np.ndarray:
        """Injects dropout defects into the frame without clipping."""
        X_out = X.copy()
        X_out[mask] -= H
        return X_out

    def inject_domain_failure(self, X: np.ndarray, mask: np.ndarray, fault_value: float = -100.0) -> np.ndarray:
        """Injects domain failures."""
        X_out = X.copy()
        X_out[mask] = fault_value
        return X_out

class CalibrationMetrics:
    @staticmethod
    def classification_loss(state: np.ndarray, truth: np.ndarray) -> float:
        """Computes multi-class cross entropy or mismatch rate."""
        return np.mean(state != truth)

    @staticmethod
    def background_loss(B: np.ndarray, B_star: np.ndarray) -> float:
        """Computes MSE background corruption ISE_B."""
        return np.sum((B - B_star)**2)

    @staticmethod
    def compute_objective(L_class: float, L_B: float, L_FPR: float, 
                          lambda_class: float=1.0, lambda_B: float=1.0, lambda_FPR: float=1.0) -> float:
        return lambda_class * L_class + lambda_B * L_B + lambda_FPR * L_FPR

    @staticmethod
    def evaluate_recall(state: np.ndarray, truth: np.ndarray, target_class: int) -> float:
        true_positives = np.sum((state == target_class) & (truth == target_class))
        actual_positives = np.sum(truth == target_class)
        return true_positives / actual_positives if actual_positives > 0 else 0.0

    @staticmethod
    def evaluate_precision(state: np.ndarray, truth: np.ndarray, target_class: int) -> float:
        true_positives = np.sum((state == target_class) & (truth == target_class))
        predicted_positives = np.sum(state == target_class)
        return true_positives / predicted_positives if predicted_positives > 0 else 0.0

if __name__ == "__main__":
    # Smoke test the synthetic generator
    gen = SyntheticFITSGenerator(shape=(50, 50))
    B_star = gen.generate_background(100.0)
    X_clean = gen.generate_clean_frame(B_star)
    
    # Inject CR
    X_cr = gen.inject_cosmic_ray(X_clean, Q=5000.0, L=10.0, phi=np.pi/4, w=1.0, x0=25, y0=25)
    
    print(f"Clean Max: {X_clean.max():.2f}")
    print(f"CR Max:    {X_cr.max():.2f}")
