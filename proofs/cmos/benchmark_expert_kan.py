import torch
import torch.nn as nn
import torch.optim as optim
import numpy as np
import time

from RecurrentExpertKAN import RecurrentExpertKAN

# Add pykan to path so we can import standard KANLayer
import sys
import os
sys.path.append(os.path.join(os.path.dirname(__file__), 'pykan'))
from kan import KANLayer

class RecurrentBaselineKAN(nn.Module):
    """
    A baseline model using the standard generic B-spline KANLayer,
    wrapped in the exact same recurrent (cdDelay) loop for a fair comparison.
    """
    def __init__(self, in_dim, hidden_dim, out_dim, layers=2):
        super().__init__()
        self.layers = nn.ModuleList([
            KANLayer(in_dim if i == 0 else hidden_dim, 
                     out_dim if i == layers - 1 else hidden_dim)
            for i in range(layers)
        ])
        
    def forward(self, x_seq):
        batch, seq_len, _ = x_seq.shape
        h_states = [torch.zeros(batch, layer.out_dim, device=x_seq.device) for layer in self.layers]
        
        outputs = []
        for t in range(seq_len):
            x_t = x_seq[:, t, :]
            
            for i, layer in enumerate(self.layers):
                # We concatenate x_t and h_{t-1} for standard KAN since it expects a single vector
                # But wait, standard KANLayer expects x as input. We need to sum the spatial and temporal,
                # or pass them concatenated. The RecurrentExpertKAN explicitly separates them.
                # To be fair, we give the Baseline KAN the concatenated input and it outputs the next hidden state.
                # Oh, actually RecurrentExpertKAN uses h_prev=h_states[i] in the forward pass.
                # KANLayer doesn't have h_prev. Let's just concatenate them if it's not the Expert layer.
                
                # To make this strictly fair, we should make a custom Baseline layer that concatenates
                pass
            
            # Since KANLayer doesn't support h_prev natively, let's wrap it
            outputs.append(h_states[-1].unsqueeze(1))
            
        return torch.cat(outputs, dim=1)

# Better: A fair recurrent wrapper for standard KAN
class BaselineKANRecurrentCell(nn.Module):
    def __init__(self, in_dim, out_dim):
        super().__init__()
        # Input is x_t and h_{t-1} concatenated
        self.kan = KANLayer(in_dim + out_dim, out_dim)
        self.out_dim = out_dim
        
    def forward(self, x, h_prev):
        xh = torch.cat([x, h_prev], dim=-1)
        # KANLayer returns (y, preacts, postacts, postspline)
        y = self.kan(xh)[0]
        return y

class RecurrentBaselineKANFair(nn.Module):
    def __init__(self, in_dim, hidden_dim, out_dim, layers=2):
        super().__init__()
        self.layers = nn.ModuleList([
            BaselineKANRecurrentCell(in_dim if i == 0 else hidden_dim, 
                                     out_dim if i == layers - 1 else hidden_dim)
            for i in range(layers)
        ])
        
    def forward(self, x_seq):
        batch, seq_len, _ = x_seq.shape
        h_states = [torch.zeros(batch, layer.out_dim, device=x_seq.device) for layer in self.layers]
        outputs = []
        for t in range(seq_len):
            x_t = x_seq[:, t, :]
            for i, layer in enumerate(self.layers):
                h_states[i] = layer(x_t if i == 0 else h_states[i-1], h_states[i])
            outputs.append(h_states[-1].unsqueeze(1))
        return torch.cat(outputs, dim=1)


def generate_synthetic_cosmic_ray_data(num_samples=1000, seq_len=20):
    """
    Generates synthetic CMOS pixel streams.
    - Read noise (Gaussian)
    - Star signal (Constant baseline with Poisson noise)
    - Cosmic ray (Sharp positive spike lasting 1-2 frames)
    
    Returns:
    X: (batch, seq_len, 1) - pixel intensities
    Y: (batch, seq_len, 1) - binary mask (1 if cosmic ray is present)
    """
    torch.manual_seed(42)
    
    # Background read noise
    X = torch.randn(num_samples, seq_len, 1) * 0.1
    
    # Star signals (constant underlying flux)
    star_flux = torch.rand(num_samples, 1, 1) * 2.0
    # Add Poisson-like noise (approximated)
    X += star_flux + torch.randn(num_samples, seq_len, 1) * torch.sqrt(star_flux + 1e-3) * 0.1
    
    # True labels
    Y = torch.zeros(num_samples, seq_len, 1)
    
    # Inject cosmic rays
    for i in range(num_samples):
        # 30% chance of a cosmic ray hit in this sequence
        if torch.rand(1).item() < 0.3:
            hit_time = torch.randint(2, seq_len - 2, (1,)).item()
            # Sudden massive energy deposit
            cr_energy = torch.rand(1).item() * 5.0 + 3.0
            X[i, hit_time, 0] += cr_energy
            # Slight decay into the next frame (charge blooming/persistence)
            X[i, hit_time+1, 0] += cr_energy * 0.2
            
            Y[i, hit_time, 0] = 1.0
            Y[i, hit_time+1, 0] = 1.0
            
    # Normalize X to be strictly positive since Bregman potentials take log(x)
    X = torch.nn.functional.softplus(X)
    return X, Y


def train_model(model, X_train, Y_train, epochs=20, lr=0.01):
    optimizer = optim.Adam(model.parameters(), lr=lr)
    scheduler = optim.lr_scheduler.CosineAnnealingLR(optimizer, T_max=epochs, eta_min=1e-5)
    criterion = nn.BCEWithLogitsLoss()
    
    model.train()
    history = []
    
    start_time = time.time()
    for epoch in range(epochs):
        optimizer.zero_grad()
        
        # Forward pass
        preds = model(X_train)
        
        # Loss
        loss = criterion(preds, Y_train)
        loss.backward()
        optimizer.step()
        scheduler.step()
        
        history.append(loss.item())
        
    duration = time.time() - start_time
    return history, duration

if __name__ == "__main__":
    print("Generating synthetic L.A. Cosmic ray dataset...")
    X, Y = generate_synthetic_cosmic_ray_data(num_samples=500, seq_len=15)
    
    print("Initializing models...")
    in_dim = 1
    hidden_dim = 4
    out_dim = 1
    
    model_expert = RecurrentExpertKAN(in_dim, hidden_dim, out_dim, layers=2)
    model_baseline = RecurrentBaselineKANFair(in_dim, hidden_dim, out_dim, layers=2)
    
    print("\n--- Training Recurrent Expert KAN ---")
    expert_loss, expert_time = train_model(model_expert, X, Y, epochs=50, lr=0.05)
    print(f"Final Loss: {expert_loss[-1]:.4f} | Time: {expert_time:.2f}s")
    
    print("\n--- Training Baseline B-Spline KAN ---")
    baseline_loss, baseline_time = train_model(model_baseline, X, Y, epochs=50, lr=0.05)
    print(f"Final Loss: {baseline_loss[-1]:.4f} | Time: {baseline_time:.2f}s")
    
    print("\n=== Benchmark Summary ===")
    print(f"Expert KAN Loss Improvement: {(baseline_loss[-1] - expert_loss[-1])/baseline_loss[-1] * 100:.1f}%")
