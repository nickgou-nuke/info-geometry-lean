import numpy as np
from dataclasses import dataclass
from typing import Tuple, Dict, Any, Optional, Union, List

@dataclass(frozen=True)
class CalibratedFrame:
    electrons: np.ndarray
    invalid_mask: np.ndarray
    saturation_mask: np.ndarray
    gain_e_per_adu: Union[np.ndarray, float]
    pedestal_adu: Union[np.ndarray, float]
    exposure_s: Optional[float]
    temperature_c: Optional[float]
    header: dict

class TemporalFITSGenerator:
    def __init__(self, shape: Tuple[int, int] = (50, 50), 
                 pedestal: float = 99.99, sigma_read: float = 3.01):
        self.shape = shape
        self.pedestal = pedestal
        self.c0 = sigma_read**2  # Read noise variance = 9.05
        self.c1 = 1.0  # Shot noise variance coefficient (Poisson)
        self.c2 = 0.0001  # Multiplicative variance
        
    def generate_latent_background(self) -> np.ndarray:
        P_p = np.ones(self.shape)
        I_t = self.pedestal
        d_pt = np.zeros(self.shape)
        F_pt = np.zeros(self.shape)
        return P_p * I_t + d_pt + F_pt

    def generate_clean_frame(self, B_star: np.ndarray) -> np.ndarray:
        # Multiplicative noise
        B_mult = B_star * np.random.normal(1.0, np.sqrt(self.c2), size=self.shape)
        # Shot noise
        poisson_shot = np.random.poisson(B_mult * self.c1) / self.c1
        # Additive read noise
        read_noise = np.random.normal(0, np.sqrt(self.c0), size=self.shape)
        return poisson_shot + read_noise

    def inject_cosmic_ray(self, X: np.ndarray, Q: float, L: float, phi: float, w: float, x0: int, y0: int) -> np.ndarray:
        X_out = X.copy()
        y_indices, x_indices = np.indices(self.shape)
        dx = x_indices - x0
        dy = y_indices - y0
        d_par = dx * np.cos(phi) + dy * np.sin(phi)
        d_perp = -dx * np.sin(phi) + dy * np.cos(phi)
        
        C_tilde = np.exp(- (d_perp**2) / (2 * w**2)) * (np.abs(d_par) <= L/2)
        C_sum = np.sum(C_tilde)
        if C_sum > 0:
            X_out += Q * (C_tilde / C_sum)
        return X_out

    def inject_dropout(self, X: np.ndarray, H: float, mask: np.ndarray) -> np.ndarray:
        X_out = X.copy()
        X_out[mask] -= H
        return X_out

from ModularAsymmetricPipeline import ModularAsymmetricCMOSPipeline, PixelClass

def calibrate_parameters(n_frames=20):
    gen = TemporalFITSGenerator()
    B_star = gen.generate_latent_background()
    
    best_loss = float('inf')
    best_params = {}
    
    domain_floor = 84.95
    
    mu_adm_range = [3.0, 5.0, 7.0]
    tau_cr_range = [15.0, 20.0, 25.0]
    tau_drop_range = [10.0, 15.0, 20.0]
    rho_range = [0.95, 0.99]
    
    # Simple grid search over thresholds
    for mu_adm in mu_adm_range:
        for tau_cr in tau_cr_range:
            for tau_drop in tau_drop_range:
                for rho in rho_range:
                    B_est = B_star.copy()
                    L_B_total = 0.0
                    L_class_total = 0.0
                    
                    pipeline = ModularAsymmetricCMOSPipeline(
                        a=1.0, b=0.0, domain_floor=domain_floor,
                        mu_admission=mu_adm, epsilon_admission=1.0,
                        tau_cosmic=tau_cr, epsilon_cosmic=2.0,
                        tau_dropout=tau_drop, epsilon_dropout=1.5
                    )
                    
                    for t in range(n_frames):
                        X = gen.generate_clean_frame(B_star)
                        truth = np.full(X.shape, PixelClass.BACKGROUND)
                        
                        # Inject Cosmic Ray
                        if t == 5:
                            X = gen.inject_cosmic_ray(X, Q=2000, L=5.0, phi=0.0, w=1.0, x0=25, y0=25)
                            truth[X > B_star + 300] = PixelClass.COSMIC
                            
                        # Inject Dropout
                        if t == 10:
                            mask = (np.random.rand(*X.shape) < 0.01)
                            X = gen.inject_dropout(X, H=50.0, mask=mask)
                            truth[mask] = PixelClass.DROPOUT
                            
                        res = pipeline.process_frame(X, B_est, np.zeros_like(X), np.zeros_like(X))
                        state = res['state']
                        r = res['responsibility']
                        
                        L_class_total += np.mean(state != truth)
                        
                        # Recursive background update (only protected by responsibility)
                        alpha_update = r * (1 - rho)
                        B_est = B_est + alpha_update * (X - B_est)
                        L_B_total += np.sum((B_est - B_star)**2)
                        
                    total_loss = L_class_total * 1000.0 + L_B_total
                    if total_loss < best_loss:
                        best_loss = total_loss
                        best_params = {'mu_adm': mu_adm, 'tau_CR': tau_cr, 'tau_drop': tau_drop, 'rho': rho}
                        
    return best_params, best_loss

if __name__ == "__main__":
    best_params, best_loss = calibrate_parameters()
    print(f"Optimal Parameters: {best_params}")
    print(f"Minimal Objective Loss: {best_loss:.2f}")
