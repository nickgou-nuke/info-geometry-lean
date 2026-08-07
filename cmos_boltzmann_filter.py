import torch
import torch.nn as nn
import matplotlib.pyplot as plt

class CMOSBoltzmannFilter(nn.Module):
    """
    The origin of the architecture: 
    Filtering CMOS pixel noise and cosmic ray spikes using 
    Deviance Boltzmann epsilon-regularized factors.
    """
    def __init__(self, epsilon=1e-3, temperature=0.1):
        super().__init__()
        self.epsilon = epsilon
        self.temperature = temperature
        
        # Historical background (H) state buffer
        self.register_buffer('historic_background', None)

    def forward(self, current_signal, mode='poisson'):
        """
        current_signal: Tensor of shape (Batch, Channels, Height, Width)
        mode: 'l2', 'poisson', or 'beta'
        """
        # Initialize background on first frame
        if self.historic_background is None or self.historic_background.shape != current_signal.shape:
            self.historic_background = current_signal.clone()
            return current_signal

        S = current_signal
        H = self.historic_background
        
        # 1. Compute Deviance (Energy Gap) based on the noise model
        if mode == 'poisson':
            # Poisson Deviance (for photon shot noise / Kullback-Leibler)
            # D(S, H) = S * log(S / H) - (S - H)
            S_safe = torch.clamp(S, min=1e-7)
            H_safe = torch.clamp(H, min=1e-7)
            deviance = S_safe * torch.log(S_safe / H_safe) - (S_safe - H_safe)
        elif mode == 'beta':
            # Beta-divergence (e.g., beta=0 Itakura-Saito for scale-invariant noise)
            # D_IS(S, H) = S / H - log(S / H) - 1
            S_safe = torch.clamp(S, min=1e-7)
            H_safe = torch.clamp(H, min=1e-7)
            deviance = (S_safe / H_safe) - torch.log(S_safe / H_safe) - 1.0
        else:
            # Standard Gaussian / L2
            deviance = torch.square(S - H)
        
        # 2. Deviance Boltzmann epsilon-regularized weighting
        # W = exp(-Deviance / epsilon)
        boltzmann_weight = torch.exp(-deviance / self.epsilon)

        
        # 3. Update Historic Background (Moving Average with Boltzmann weight)
        # Cosmic rays are rejected (weight ~ 0), background is preserved.
        new_background = self.historic_background * (1.0 - boltzmann_weight) + current_signal * boltzmann_weight
        
        self.historic_background = new_background.detach()
        
        return new_background

if __name__ == "__main__":
    print("🌌 CMOS Boltzmann Regularized Cosmic Ray Filter 🌌")
    
    # 1D CMOS sensor array with 100 pixels
    sensor_size = 100
    filter_layer = CMOSBoltzmannFilter(epsilon=1e-3, temperature=0.05)
    
    # Generate a stable historic background
    background = torch.sin(torch.linspace(0, 3.14, sensor_size))
    filter_layer(background.view(1, 1, 1, -1)) # Initialize history
    
    # Generate new frame with thermal noise AND a cosmic ray spike
    new_frame = background.clone()
    new_frame += torch.randn(sensor_size) * 0.05 # Thermal noise
    new_frame[50] = 5.0 # HUGE Cosmic Ray Spike at pixel 50!
    
    # Apply Filters
    cleaned_poisson = filter_layer(new_frame.view(1, 1, 1, -1), mode='poisson').flatten()
    
    # Reset background for second test
    filter_layer.historic_background = background.clone().view(1, 1, 1, -1)
    cleaned_beta = filter_layer(new_frame.view(1, 1, 1, -1), mode='beta').flatten()
    
    print(f"[*] Cosmic Ray Spike (Raw Sensor) : {new_frame[50].item():.2f}")
    print(f"[*] Cosmic Ray Spike (Poisson)    : {cleaned_poisson[50].item():.2f}")
    print(f"[*] Cosmic Ray Spike (Beta-0/IS)  : {cleaned_beta[50].item():.2f}")
    
    if cleaned_poisson[50].item() < 1.1:
        print("[+] SUCCESS: The Poisson Deviance Boltzmann weight successfully rejected the cosmic ray!")
