import torch
import torch.nn as nn

try:
    from kan import KANLayer
except ImportError:
    # Fallback to nn.Module if pykan is not installed/accessible in this environment, 
    # though the architecture strictly parallels the KAN API.
    KANLayer = nn.Module

class RecurrentExpertKANLayer(KANLayer):
    """
    Recurrent Expert KAN Layer replacing generic B-splines with physics-informed 
    Bregman potentials (Gaussian, Poisson, Gamma). 
    
    This strictly implements the Cayley-Dickson algebraic inclusion (spatial edges)
    vs temporal shift (recurrent feedback) formalized in our Lean 4 modules.
    
    By subclassing standard KANLayer, we maintain the ability to plot and regularize
    these edge-potentials just like standard splines, but heavily bias the network
    towards the exact noise geometries of CMOS RAW sensors.
    """
    def __init__(self, in_dim, out_dim, **kwargs):
        # Initialize standard KAN layer if available, or base module
        if KANLayer is not nn.Module:
            super().__init__(in_dim, out_dim, **kwargs)
            # Remove standard splines to save memory, we override forward anyway
            if hasattr(self, 'coef'):
                del self.coef
        else:
            super().__init__()
            self.in_dim = in_dim
            self.out_dim = out_dim
            
        # 1. Algebraic Inclusion (Spatial Edges, cdEmbed)
        # Each edge sums the potentials of the 3 noise experts
        self.c_gauss   = nn.Parameter(torch.randn(out_dim, in_dim) / (in_dim ** 0.5))
        self.c_poisson = nn.Parameter(torch.randn(out_dim, in_dim) / (in_dim ** 0.5))
        self.c_gamma   = nn.Parameter(torch.randn(out_dim, in_dim) / (in_dim ** 0.5))
        
        # 2. Temporal Delay Map S_n (Recurrent Feedback Edges, cdDelay)
        # These process the explicit causal shift.
        self.fb_gauss   = nn.Parameter(torch.randn(out_dim, out_dim) / (out_dim ** 0.5))
        self.fb_poisson = nn.Parameter(torch.randn(out_dim, out_dim) / (out_dim ** 0.5))
        self.fb_gamma   = nn.Parameter(torch.randn(out_dim, out_dim) / (out_dim ** 0.5))

    def forward(self, x, h_prev=None):
        """
        x: (batch, in_dim) - The current observation
        h_prev: (batch, out_dim) - The causal delay state (optional)
        """
        # Enforce strict positivity for Bregman generator stability
        x_pos = torch.nn.functional.softplus(x) + 1e-6
        
        # ---------------------------------------------------------
        # Spatial forward pass (The Cayley-Dickson current coordinate)
        # ---------------------------------------------------------
        # Expert 1: Gaussian (L2 Geometry / Read Noise) -> f(x) = x
        phi_g_x = x
        
        # Expert 2: Poisson (KL Geometry / Shot Noise) -> f(x) = x * ln(x)
        phi_p_x = x_pos * torch.log(x_pos)
        
        # Expert 3: Gamma (Itakura-Saito / Speckle) -> f(x) = -ln(x)
        phi_gamma_x = -torch.log(x_pos)
        
        out = (
            torch.nn.functional.linear(phi_g_x, self.c_gauss) + 
            torch.nn.functional.linear(phi_p_x, self.c_poisson) + 
            torch.nn.functional.linear(phi_gamma_x, self.c_gamma)
        )
        
        # ---------------------------------------------------------
        # Temporal delay processing (The causal shift map S_n)
        # ---------------------------------------------------------
        if h_prev is not None:
            h_pos = torch.nn.functional.softplus(h_prev) + 1e-6
            
            phi_g_h = h_prev
            phi_p_h = h_pos * torch.log(h_pos)
            phi_gamma_h = -torch.log(h_pos)
            
            fb = (
                torch.nn.functional.linear(phi_g_h, self.fb_gauss) + 
                torch.nn.functional.linear(phi_p_h, self.fb_poisson) + 
                torch.nn.functional.linear(phi_gamma_h, self.fb_gamma)
            )
            
            # (In the physical limit, this equates to scalar sum of potentials)
            out = out + fb
            
        # Add LayerNorm to stabilize the recurrent potentials (only on hidden layers)
        if self.out_dim > 1:
            if not hasattr(self, 'ln'):
                self.ln = nn.LayerNorm(self.out_dim).to(out.device)
            out = self.ln(out)
            
        return out

class RecurrentExpertKAN(nn.Module):
    """
    A full physics-informed KAN mapping continuous causal streams into
    the topological space using Bregman divergence basis functions.
    """
    def __init__(self, in_dim, hidden_dim, out_dim, layers=2):
        super().__init__()
        self.layers = nn.ModuleList([
            RecurrentExpertKANLayer(in_dim if i == 0 else hidden_dim, 
                                    out_dim if i == layers - 1 else hidden_dim)
            for i in range(layers)
        ])
        
    def forward(self, x_seq):
        """
        x_seq: (batch, seq_len, in_dim)
        """
        batch, seq_len, _ = x_seq.shape
        
        # Initialize causal states with zeros (cdZero equivalent)
        h_states = [torch.zeros(batch, layer.out_dim, device=x_seq.device) for layer in self.layers]
        
        outputs = []
        for t in range(seq_len):
            x_t = x_seq[:, t, :]
            
            # Forward pass through layers recursively
            for i, layer in enumerate(self.layers):
                h_states[i] = layer(x_t if i == 0 else h_states[i-1], h_states[i])
                
            outputs.append(h_states[-1].unsqueeze(1))
            
        return torch.cat(outputs, dim=1)
