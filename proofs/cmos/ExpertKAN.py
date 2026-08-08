import torch
import torch.nn as nn
from kan.KANLayer import KANLayer
from kan.MLP import MLP

class ExpertKANLayer(nn.Module):
    """
    Subclassing/Replacing standard KANLayer with Bregman Experts.
    """
    def __init__(self, in_dim, out_dim):
        super().__init__()
        self.in_dim = in_dim
        self.out_dim = out_dim
        
        # Coefficients for the 3 experts: Gaussian, Poisson, Gamma
        self.coef = nn.Parameter(torch.randn(out_dim, in_dim, 3) / in_dim)

    def forward(self, x):
        """
        x: (batch, in_dim)
        """
        batch = x.shape[0]
        # Make x strictly positive for Poisson and Gamma
        x_pos = torch.nn.functional.softplus(x) + 1e-4
        
        # Compute experts
        # Gaussian: x
        phi_g = x_pos
        # Poisson: x * log(x)
        phi_p = x_pos * torch.log(x_pos)
        # Gamma: -log(x)
        phi_gamma = -torch.log(x_pos)
        
        # Stack experts: (batch, in_dim, 3)
        experts = torch.stack([phi_g, phi_p, phi_gamma], dim=-1)
        
        # Multiply by coefficients and sum over experts and in_dim
        # experts: (batch, in_dim, 3)
        # coef: (out_dim, in_dim, 3)
        # We want y: (batch, out_dim)
        y = torch.einsum('b i e, o i e -> b o', experts, self.coef)
        
        return y, None, None, None # Match KANLayer return signature if needed

class RecurrentExpertKAN(nn.Module):
    def __init__(self, in_dim, hidden_dim, out_dim):
        super().__init__()
        # The input to the hidden layer is [x_t, h_{t-1}], so dim is in_dim + hidden_dim
        self.layer1 = ExpertKANLayer(in_dim + hidden_dim, hidden_dim)
        self.layer2 = ExpertKANLayer(hidden_dim, out_dim)
        
    def forward(self, x_seq):
        """
        x_seq: (batch, seq_len, in_dim)
        """
        batch, seq_len, _ = x_seq.shape
        h = torch.zeros(batch, self.layer1.out_dim, device=x_seq.device)
        
        outputs = []
        for t in range(seq_len):
            x_t = x_seq[:, t, :]
            # Combine input and previous state
            xh = torch.cat([x_t, h], dim=-1)
            h, _, _, _ = self.layer1(xh)
            out, _, _, _ = self.layer2(h)
            outputs.append(out.unsqueeze(1))
            
        return torch.cat(outputs, dim=1)

if __name__ == "__main__":
    print("Testing Recurrent Expert KAN...")
    model = RecurrentExpertKAN(in_dim=1, hidden_dim=4, out_dim=1)
    
    # Dummy sequence data: (batch=2, seq_len=10, in_dim=1)
    dummy_input = torch.randn(2, 10, 1)
    
    out = model(dummy_input)
    print(f"Output shape: {out.shape}")
    print("Test passed successfully!")
