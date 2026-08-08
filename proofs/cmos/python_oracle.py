import numpy as np
from scipy.integrate import quad
from typing import Tuple, Dict

class CmosEstimatorOracle:
    def __init__(self, c0: float, c1: float, c2: float,
                 pi_G: float, pi_P: float, pi_I: float,
                 T_beta: float, rho: float, rho_C: float,
                 c_t: float, eps_t: float, shape: Tuple[int, int] = (1, 1)):
        assert c0 > 0
        assert c1 >= 0
        assert c2 >= 0
        self.c0 = c0
        self.c1 = c1
        self.c2 = c2
        
        self.pi_G = pi_G
        self.pi_P = pi_P
        self.pi_I = pi_I
        self.T_beta = T_beta
        
        self.rho = rho
        self.rho_C = rho_C
        
        self.c_t = c_t
        self.eps_t = eps_t
        self.shape = shape
        
        # State Arrays
        self.N_t = np.zeros(shape, dtype=np.float64)
        self.mu_t = np.zeros(shape, dtype=np.float64)
        
        self.C2_t = np.zeros(shape, dtype=np.float64)
        self.C3_t = np.zeros(shape, dtype=np.float64)
        self.C4_t = np.zeros(shape, dtype=np.float64)
        
        self.C_G = np.zeros(shape, dtype=np.float64)
        self.C_P = np.zeros(shape, dtype=np.float64)
        self.C_I = np.zeros(shape, dtype=np.float64)
        
        self.w_G = np.full(shape, pi_G, dtype=np.float64)
        self.w_P = np.full(shape, pi_P, dtype=np.float64)
        self.w_I = np.full(shape, pi_I, dtype=np.float64)
        
        # Initialize flags
        self.is_initialized = np.zeros(shape, dtype=bool)

    def variance(self, u: np.ndarray) -> np.ndarray:
        return self.c0 + self.c1 * u + self.c2 * u**2

    def d_G(self, x: np.ndarray, mu: np.ndarray) -> np.ndarray:
        # Gaussian Bregman divergence
        return 0.5 * (x - mu)**2 / self.c0

    def d_P(self, x: np.ndarray, mu: np.ndarray) -> np.ndarray:
        # Poisson Bregman divergence
        res = np.zeros_like(x)
        mask = (x > 0) & (mu > 0)
        res[mask] = x[mask] * np.log(x[mask] / mu[mask]) - x[mask] + mu[mask]
        mask_zero = (x == 0) & (mu > 0)
        res[mask_zero] = mu[mask_zero]
        return res

    def d_I(self, x: np.ndarray, mu: np.ndarray) -> np.ndarray:
        # Gamma/Itakura-Saito Bregman divergence
        res = np.full_like(x, np.inf)
        mask = (x > 0) & (mu > 0)
        res[mask] = x[mask] / mu[mask] - np.log(x[mask] / mu[mask]) - 1.0
        return res
            
    def update(self, x: np.ndarray, is_clipped: np.ndarray = None) -> Tuple[np.ndarray, np.ndarray]:
        if is_clipped is None:
            is_clipped = np.zeros_like(x, dtype=bool)
            
        uninitialized = ~self.is_initialized
        if np.any(uninitialized):
            self.mu_t[uninitialized] = x[uninitialized]
            self.N_t[uninitialized] = 0.0
            self.is_initialized[uninitialized] = True
            
        # 1. Expert divergences
        z_G = self.d_G(x, self.mu_t)
        z_P = self.d_P(x, self.mu_t)
        z_I = self.d_I(x, self.mu_t)
        
        # Handle infs
        z_I = np.nan_to_num(z_I, posinf=1e9)
        
        # 2. Combined energy
        D_t = self.w_G * z_G + self.w_P * z_P + self.w_I * z_I
        
        # 3. Admission responsibility (Fermi-Boltzmann)
        r_t = np.zeros_like(x, dtype=np.float64)
        valid = ~is_clipped
        r_t[valid] = 1.0 / (1.0 + np.exp(-(self.c_t - D_t[valid]) / self.eps_t))
        
        # Detected cosmic ray mask
        crmask = r_t < 0.5  # Boolean mask of cosmic rays
        
        # 4. Expert score updates
        self.C_G = self.rho_C * self.C_G + r_t * z_G
        self.C_P = self.rho_C * self.C_P + r_t * z_P
        self.C_I = self.rho_C * self.C_I + r_t * z_I
        
        # 5. Softmax selector weights
        logits_G = -self.C_G / self.T_beta + np.log(self.pi_G)
        logits_P = -self.C_P / self.T_beta + np.log(self.pi_P)
        logits_I = -self.C_I / self.T_beta + np.log(self.pi_I)
        
        max_logits = np.maximum.reduce([logits_G, logits_P, logits_I])
        
        exp_G = np.exp(logits_G - max_logits)
        exp_P = np.exp(logits_P - max_logits)
        exp_I = np.exp(logits_I - max_logits)
        
        sum_exp = exp_G + exp_P + exp_I
        self.w_G = exp_G / sum_exp
        self.w_P = exp_P / sum_exp
        self.w_I = exp_I / sum_exp
        
        # 6. Central moments update
        W_a = self.rho * self.N_t
        C2_a = self.rho * self.C2_t
        C3_a = self.rho * self.C3_t
        C4_a = self.rho * self.C4_t
        
        W_prime = W_a + r_t
        delta = x - self.mu_t
        
        update_mask = W_prime > 0
        if np.any(update_mask):
            wp = W_prime[update_mask]
            rt = r_t[update_mask]
            wa = W_a[update_mask]
            d = delta[update_mask]
            
            self.mu_t[update_mask] += (rt / wp) * d
            
            c2a = C2_a[update_mask]
            self.C2_t[update_mask] = c2a + (d**2) * (wa * rt) / wp
            
            c3a = C3_a[update_mask]
            self.C3_t[update_mask] = c3a + (d**3) * (wa * rt * (wa - rt)) / (wp**2) - \
                        3 * d * (rt * c2a) / wp
                        
            c4a = C4_a[update_mask]
            self.C4_t[update_mask] = c4a + (d**4) * (wa * rt * (wa**2 - wa * rt + rt**2)) / (wp**3) + \
                        6 * (d**2) * (rt**2 * c2a) / (wp**2) - \
                        4 * d * (rt * c3a) / wp
        
        self.N_t = W_prime
        
        return self.mu_t.copy(), crmask

def process_image_stack(image_stack: np.ndarray, **kwargs) -> Tuple[np.ndarray, np.ndarray]:
    """
    Process a 3D image stack (time, y, x) and return the final cleaned background image and a combined CR mask.
    """
    T, H, W = image_stack.shape
    oracle = CmosEstimatorOracle(shape=(H, W), **kwargs)
    
    cleanarr = np.zeros((H, W), dtype=np.float64)
    crmask_total = np.zeros((H, W), dtype=bool)
    
    for t in range(T):
        frame = image_stack[t]
        cleanarr, crmask = oracle.update(frame)
        crmask_total |= crmask
        
    return cleanarr, crmask_total

if __name__ == "__main__":
    # Test on a simulated 10x10 sequence of 20 frames
    np.random.seed(42)
    T, H, W = 20, 10, 10
    
    c0 = 10.0
    c1 = 0.5
    c2 = 0.01
    
    # Simulate Gaussian data
    base_mu = 100.0
    variance = c0 + c1 * base_mu + c2 * base_mu**2
    data = np.random.normal(base_mu, np.sqrt(variance), size=(T, H, W))
    
    # Inject some cosmic rays in frame 10
    data[10, 5, 5] = 5000.0
    data[10, 2, 8] = 4000.0
    
    cleanarr, crmask = process_image_stack(
        data,
        c0=c0, c1=c1, c2=c2,
        pi_G=0.333, pi_P=0.333, pi_I=0.334,
        T_beta=1.0, rho=0.99, rho_C=0.95,
        c_t=20.0, eps_t=2.0
    )
    
    print("Cosmic ray injected at (5, 5) and (2, 8).")
    print("Detection mask at those locations:")
    print(f"(5, 5): {crmask[5, 5]}")
    print(f"(2, 8): {crmask[2, 8]}")
    print(f"Number of cosmic rays detected: {np.sum(crmask)}")
