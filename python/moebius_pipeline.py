import numpy as np
from scipy.ndimage import laplace

def stable_sigmoid(x):
    """Numerically stable sigmoid function."""
    # Ensure no overflow in exp by clipping to a safe range
    x_clip = np.clip(x, -500, 500)
    return np.where(x_clip >= 0, 
                    1 / (1 + np.exp(-x_clip)), 
                    np.exp(x_clip) / (1 + np.exp(x_clip)))

def logit(p):
    """Logit function with clipping for numerical stability."""
    p_clip = np.clip(p, 1e-15, 1 - 1e-15)
    return np.log(p_clip / (1 - p_clip))

def affine_deviance(X, B, a, b):
    """
    Affine quasi-deviance for CMOS sensor noise.
    V(μ) = aμ + b
    D_{a,b}(X | B) = (2 / a^2) * ((a*X + b) * log((a*X + b) / (a*B + b)) - a*(X - B))
    """
    # X and B can be negative (we do not clip negative measurements)
    # We must ensure (a*X + b) and (a*B + b) are positive for the log
    # In practice, if a measurement is extremely negative, it might violate this.
    # We use a small epsilon offset to prevent log(<=0).
    eps = 1e-10
    aX_b = np.maximum(a * X + b, eps)
    aB_b = np.maximum(a * B + b, eps)
    
    return (2 / (a**2)) * (aX_b * np.log(aX_b / aB_b) - a * (X - B))

def spatial_laplacian(X):
    """
    Compute the spatial Laplacian filter.
    Returns L_feat.
    """
    # Simple discrete Laplacian
    return laplace(X)

def spatial_whitening(L_feat, B, a, b, k_L):
    """
    Compute spatial whitening using Laplacian and quasi-deviance variance scaling.
    L^2 normalized by variance.
    """
    var_B = np.maximum(a * B + b, 1e-10)
    # L_feat squared normalized by local variance. k_L is the weighting parameter.
    return k_L * (L_feat**2) / var_B

class MoebiusJaynesPipeline:
    def __init__(self, a, b, k_L, mu_c, eps, tau_cr, rho=1.0):
        self.a = a
        self.b = b
        self.k_L = k_L
        self.mu_c = mu_c
        self.eps = eps
        self.tau_cr = tau_cr
        self.rho = rho
        
        # State variables
        self.S = None  # Sum
        self.N = None  # Mass
        
    def initialize(self, first_frame):
        # Initialize background safely
        self.S = np.copy(first_frame)
        self.N = np.ones_like(first_frame)
        
    def get_background(self):
        # B = S / N
        N_safe = np.maximum(self.N, 1e-10)
        return self.S / N_safe
        
    def process_frame(self, X):
        B = self.get_background()
        
        # 1. Deviance computation
        # Temporal deviance D_{a,b}(X | B)
        D_temp = affine_deviance(X, B, self.a, self.b)
        
        # Spatial deviance 
        L_feat = spatial_laplacian(X)
        D_spat = spatial_whitening(L_feat, B, self.a, self.b, self.k_L)
        
        # Total distance d
        d = D_temp + D_spat
        
        # 2. Evidence gap encoding
        # r = bayesUpdate(b, alpha) = sigmoid((mu_c - d) / eps)
        r = stable_sigmoid((self.mu_c - d) / self.eps)
        
        # 3. Recursive barycenter update
        # S_t = rho * S_prev + r * X
        # N_t = rho * N_prev + r
        self.S = self.rho * self.S + r * X
        self.N = self.rho * self.N + r
        
        # 4. CR mask (anomaly detection)
        # logit(p_CR) = d / eps - mu_c / eps ?
        # Wait, evidence gap encode gives probability of background.
        # Probability of CR is 1 - r.
        # If r is small, d is large.
        # tau_cr is the threshold on d or threshold on r?
        # Usually tau_cr is threshold on d directly, or CR mask = (d > tau_cr)
        cr_mask = d > self.tau_cr
        
        return self.get_background(), cr_mask, r

