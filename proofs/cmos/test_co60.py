import torch
import numpy as np
from gamma_coincidence_nmtf import SinkhornPoissonNMTF, poisson_nll_loss
import time

def test_co60():
    torch.manual_seed(42)
    np.random.seed(42)
    
    # 250x250 channels
    N = 250
    # Two true energy states (1.17 MeV and 1.33 MeV), let's map them to channel 117 and 133
    
    # Let's say we have 3 latent energy levels to allow a fully structured matrix
    # State 0: 1.17 MeV (channel 117)
    # State 1: 1.33 MeV (channel 133)
    # State 2: Background noise state (channel 50)
    
    num_states = 3
    
    # True U and V profiles (Gaussian peaks)
    channels = torch.arange(N).float()
    
    U_true = torch.zeros(N, num_states)
    V_true = torch.zeros(N, num_states)
    
    def gaussian(x, mu, sigma):
        return torch.exp(-0.5 * ((x - mu) / sigma)**2)
        
    U_true[:, 0] = gaussian(channels, 117, 3.0)
    U_true[:, 1] = gaussian(channels, 133, 3.0)
    U_true[:, 2] = gaussian(channels, 50, 10.0) # Broad blob
    
    U_true = U_true / (U_true.sum(dim=0, keepdim=True) + 1e-9)
    V_true = U_true.clone() # Same detector
    
    # True Coupling Matrix P (Co-60 Cascade: strong correlation between 117 and 133)
    # State 0 and 1 are correlated (1.17 and 1.33 coincidence)
    P_true = torch.zeros(num_states, num_states)
    P_true[0, 1] = 0.45
    P_true[1, 0] = 0.45
    # Weak accidental coincidences or other transitions
    P_true[0, 0] = 0.02
    P_true[1, 1] = 0.02
    P_true[2, 2] = 0.06
    
    # Scale P to be a probability distribution
    P_true = P_true / P_true.sum()
    
    I_total = 100000.0 # Total counts
    
    Lambda_signal = I_total * torch.matmul(U_true, torch.matmul(P_true, V_true.t()))
    B_true = torch.ones(N, N) * 1.0 # Uniform background of 1 count per bin
    
    Lambda_true = Lambda_signal + B_true
    
    # Generate Poisson synthetic data
    X = torch.poisson(Lambda_true)
    
    print(f"Synthetic Co-60 Dataset Generated: {X.sum().item():.0f} total counts")
    
    # Initialize the NMTF Engine
    model = SinkhornPoissonNMTF(num_channels_x=N, num_channels_y=N, num_states=num_states)
    
    # Define a Physics Prior Cost Matrix C (optional, can be all zeros for fully blind)
    # Let's say we don't know the exact coupling, but we know self-transitions (0->0, 1->1) are less likely
    C = torch.zeros(num_states, num_states)
    C[0, 0] = 2.0
    C[1, 1] = 2.0
    
    optimizer = torch.optim.Adam(model.parameters(), lr=0.05)
    
    num_epochs = 100
    epsilons = torch.linspace(1.0, 0.01, num_epochs)
    
    print("Beginning Log-Sinkhorn Poisson NMTF Annealing...")
    t0 = time.time()
    for epoch in range(num_epochs):
        optimizer.zero_grad()
        
        eps = epsilons[epoch]
        Lambda_pred, P_pred, U_pred, V_pred, B_pred = model(C, eps, I_total)
        
        loss = poisson_nll_loss(X, Lambda_pred)
        
        loss.backward()
        optimizer.step()
        
        if epoch % 10 == 0 or epoch == num_epochs - 1:
            print(f"Epoch {epoch:3d} | eps = {eps:.3f} | Loss = {loss.item():.4f}")
            
    t1 = time.time()
    print(f"Annealing complete in {t1 - t0:.2f} seconds.")
    
    # Print the recovered transport plan P vs true P
    print("\nTrue Latent Coupling P:")
    print(torch.round(P_true * 100) / 100)
    
    print("\nRecovered Sinkhorn Transport Plan P (eps=0.01):")
    print(torch.round(P_pred.detach() * 100) / 100)

if __name__ == "__main__":
    test_co60()
