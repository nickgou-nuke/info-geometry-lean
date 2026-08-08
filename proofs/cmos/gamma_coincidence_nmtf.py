import torch
import torch.nn as nn
import torch.nn.functional as F

class LogSinkhornCoupling(nn.Module):
    """
    Numerically stable Differentiable Sinkhorn Optimal Transport.
    Operates entirely in the log-domain to survive ε -> 0 annealing.
    """
    def __init__(self, num_iters=20):
        super().__init__()
        self.num_iters = num_iters

    def forward(self, C, log_r, log_c, epsilon):
        # Initialize dual variables f and g to zeros
        f = torch.zeros_like(log_r)
        g = torch.zeros_like(log_c)

        for _ in range(self.num_iters):
            # Update f: ε * log(r) - ε * logsumexp((g - C) / ε)
            f = epsilon * log_r - epsilon * torch.logsumexp((g.unsqueeze(0) - C) / epsilon, dim=1)
            # Update g: ε * log(c) - ε * logsumexp((f - C) / ε)
            g = epsilon * log_c - epsilon * torch.logsumexp((f.unsqueeze(1) - C) / epsilon, dim=0)

        # Reconstruct the transport plan P = diag(exp(f/ε)) * exp(-C/ε) * diag(exp(g/ε))
        # P_{ij} = exp((f_i + g_j - C_{ij}) / ε)
        log_P = (f.unsqueeze(1) + g.unsqueeze(0) - C) / epsilon
        return torch.exp(log_P)


class SinkhornPoissonNMTF(nn.Module):
    def __init__(self, num_channels_x, num_channels_y, num_states, base_U=None, base_V=None):
        super().__init__()
        self.num_states = num_states
        
        # Marginal intensities (Total counts for each state transition)
        # Parameterized in log-space to enforce strict non-negativity
        self.log_r = nn.Parameter(torch.randn(num_states))
        self.log_c = nn.Parameter(torch.randn(num_states))
        
        # Detector Profiles (Semi-blind: Base HPGe profile + Learned non-negative perturbation)
        self.base_U = base_U if base_U is not None else torch.zeros(num_channels_x, num_states)
        self.base_V = base_V if base_V is not None else torch.zeros(num_channels_y, num_states)
        
        self.delta_U = nn.Parameter(torch.randn(num_channels_x, num_states) * 0.01)
        self.delta_V = nn.Parameter(torch.randn(num_channels_y, num_states) * 0.01)
        
        # Smooth Background Components
        self.bg_base = nn.Parameter(torch.zeros(num_channels_x, num_channels_y))
        
        self.sinkhorn = LogSinkhornCoupling(num_iters=25)

    def get_profiles(self):
        # Softplus ensures strict non-negativity for the detector response functions
        U = F.softplus(self.base_U + self.delta_U)
        V = F.softplus(self.base_V + self.delta_V)
        # L1 normalize columns so scale is entirely handled by the transport plan P
        U = U / (U.sum(dim=0, keepdim=True) + 1e-9)
        V = V / (V.sum(dim=0, keepdim=True) + 1e-9)
        return U, V

    def forward(self, C, epsilon, I_total):
        """
        C: Cost matrix (Physics Priors). C_ij = inf means forbidden transition.
        epsilon: Entropy temperature (Annealed -> 0).
        I_total: Global scalar for total coincidence counts.
        """
        U, V = self.get_profiles()
        
        # Softmax over the marginals to ensure they are valid probability distributions (sum to 1)
        log_r_norm = F.log_softmax(self.log_r, dim=0)
        log_c_norm = F.log_softmax(self.log_c, dim=0)
        
        # 1. Generate the Physics-Constrained Latent Coupling P via Log-Sinkhorn
        P = self.sinkhorn(C, log_r_norm, log_c_norm, epsilon)
        
        # 2. Project the latent coupling through the detector profiles
        # Λ_signal = U @ P @ V^T
        Lambda_signal = torch.matmul(U, torch.matmul(P, V.t()))
        
        # 3. Add smooth background
        B = F.softplus(self.bg_base)
        
        # Total Expectation Model
        Lambda = I_total * Lambda_signal + B
        return Lambda, P, U, V, B

def poisson_nll_loss(X, Lambda):
    """ Standard β=1 Divergence (Poisson Negative Log-Likelihood) up to a constant """
    # X * log(Lambda) - Lambda
    return torch.mean(Lambda - X * torch.log(Lambda + 1e-9))
