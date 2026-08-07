import torch
import torch.nn as nn
import torch.optim as optim
import sys
import os
import time

try:
    from astropy.io import fits
    HAS_ASTROPY = True
except ImportError:
    print("Warning: astropy not found, unable to load real FITS files. (pip install astropy)")
    HAS_ASTROPY = False

from twistor_pytorch_layer import TwistorVisionTransformer

def load_fits_data(filepath, device='cuda'):
    if not HAS_ASTROPY:
        print("Mocking data since astropy is missing.")
        # Return a mock tensor
        return torch.randn(1, 1, 256, 256, device=device)
        
    if not os.path.exists(filepath):
        print(f"Warning: FITS file {filepath} not found. Using mock data.")
        return torch.randn(1, 1, 256, 256, device=device)
        
    print(f"[*] Loading FITS data from {filepath}...")
    with fits.open(filepath) as hdul:
        # Assuming the image is in the primary HDU
        data = hdul[0].data
        
    # Convert to torch tensor, fix byte order if necessary, add dims, move to device
    if data.dtype.byteorder == '>':
        data = data.byteswap().view(data.dtype.newbyteorder())
    tensor_data = torch.from_numpy(data).float()
    
    # Resize to something manageable for a quick test if it's too large, or just keep it
    # We will slice a 1024x1024 region if it's too big
    if tensor_data.dim() == 2:
        H, W = tensor_data.shape
        if H > 1024 or W > 1024:
            tensor_data = tensor_data[:1024, :1024]
        tensor_data = tensor_data.unsqueeze(0).unsqueeze(0)
    
    # Normalize to [0, 1] range for stability
    t_min, t_max = tensor_data.min(), tensor_data.max()
    tensor_data = (tensor_data - t_min) / (t_max - t_min + 1e-8)
    
    return tensor_data.to(device)

def run_pinn_epoch():
    print("====================================================")
    print("🌌 TWISTOR PINN (TF32) - EXPERIMENTAL EPOCH 🌌")
    print("====================================================")
    
    device = torch.device('cuda' if torch.cuda.is_available() else 'cpu')
    print(f"[+] Using device: {device}")
    
    # Enable TF32 for optimal performance on Tensor Cores
    if torch.cuda.is_available():
        torch.backends.cuda.matmul.allow_tf32 = True
        torch.backends.cudnn.allow_tf32 = True
        print("[+] NVIDIA TensorFloat-32 (TF32) enabled.")
        
    model = TwistorVisionTransformer().to(device)
    optimizer = optim.Adam(model.parameters(), lr=1e-3)
    
    # Target file
    fits_file = "james_webb_twistor_clean.fits"
    
    input_tensor = load_fits_data(fits_file, device=device)
    print(f"[+] Input tensor shape: {input_tensor.shape}, precision: {input_tensor.dtype}")
    
    print("[*] Starting Forward Pass (Hodge Duality Twist)...")
    torch.cuda.synchronize() if device.type == 'cuda' else None
    start_time = time.perf_counter()
    
    output = model(input_tensor)
    
    torch.cuda.synchronize() if device.type == 'cuda' else None
    forward_time = time.perf_counter() - start_time
    print(f"[+] Forward pass completed in {forward_time*1000:.2f} ms")
    
    print("[*] Starting Backward Pass (Autograd Gradient Descent)...")
    loss = output.sum() # Dummy loss for demonstration
    
    optimizer.zero_grad()
    
    torch.cuda.synchronize() if device.type == 'cuda' else None
    start_time = time.perf_counter()
    
    loss.backward()
    optimizer.step()
    
    torch.cuda.synchronize() if device.type == 'cuda' else None
    backward_time = time.perf_counter() - start_time
    
    print(f"[+] Backward pass completed in {backward_time*1000:.2f} ms")
    print(f"[+] Gradients successfully propagated! Conv1 grad norm: {model.conv1.weight.grad.norm().item():.5f}")
    
    print("====================================================")
    print("✅ EPOCH SUCCESSFUL! Twistor Geometry is Executable.")
    print("====================================================")

    import matplotlib.pyplot as plt
    import numpy as np
    import os

    print("\n🎨 Стартиране на Визуализационния и Експортен Модул...")

    # 1. Екстракция на каналите (0: SA/Енергия, 3: SkewSA/Фаза)
    # F_out requires extraction from TwistorVisionTransformer.
    # Wait, TwistorVisionTransformer output shape is [1, 1, H, W] for the toy demo. 
    # Let's extract the intermediate TwistorMaxwellLayer output instead!
    # But for a simple test, we will just pass input_tensor through TwistorModularFlowFunction
    print("[+] Пропускане през чист TwistorModularFlowFunction за визуализация...")
    from twistor_pytorch_layer import TwistorModularFlowFunction
    F_vis_input = torch.zeros(1, 4, input_tensor.shape[2], input_tensor.shape[3], device=device)
    F_vis_input[:, 0:1, :, :] = input_tensor
    F_out = TwistorModularFlowFunction.apply(F_vis_input, 0.15)
    
    energy_out = F_out[0, 0, :, :].detach().cpu().numpy()
    phase_out = F_out[0, 3, :, :].detach().cpu().numpy()

    # 2. Запазване на научен FITS файл
    print("[+] Експортиране на 32-битов научен тензор в 'james_webb_twistor_processed.fits'...")
    hdu_primary = fits.PrimaryHDU()
    hdu_energy = fits.ImageHDU(energy_out, name='ENERGY_SA')
    hdu_phase = fits.ImageHDU(phase_out, name='PHASE_SKEWSA')
    hdul = fits.HDUList([hdu_primary, hdu_energy, hdu_phase])
    hdul.writeto("james_webb_twistor_processed.fits", overwrite=True)

    # 3. Генериране на PNG Визуализация
    print("[+] Генериране на визуална съпоставка в 'twistor_jwst_visualization.png'...")
    fig, axes = plt.subplots(1, 2, figsize=(16, 8))
    fig.suptitle("Hestenes Conformal Twistor Filter: JWST Data", fontsize=20, fontweight='bold')

    vmax_e = np.percentile(energy_out, 99.5)
    vmin_e = np.percentile(energy_out, 0.5)

    ax1 = axes[0]
    im1 = ax1.imshow(energy_out, cmap='inferno', vmin=vmin_e, vmax=vmax_e, origin='lower')
    ax1.set_title("Twistor Filtered SA (Reconstructed Energy)")
    plt.colorbar(im1, ax=ax1, fraction=0.046, pad=0.04)

    ax2 = axes[1]
    im2 = ax2.imshow(phase_out, cmap='twilight_shifted', origin='lower')
    ax2.set_title("Twistor Filtered SkewSA (Topological Phase)")
    plt.colorbar(im2, ax=ax2, fraction=0.046, pad=0.04)

    for ax in axes.flat:
        ax.axis('off')

    plt.tight_layout()
    plt.savefig("twistor_jwst_visualization.png", dpi=300, bbox_inches='tight')
    plt.close()

    print("🏆 УСПЕХ! Всички визуални и научни файлове са запазени.")

if __name__ == "__main__":
    run_pinn_epoch()
