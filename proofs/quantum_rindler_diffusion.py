import numpy as np
import cv2
import matplotlib.pyplot as plt

def generate_medical_phantom():
    img = np.zeros((256, 256), dtype=np.float64)
    cv2.circle(img, (128, 128), 100, 180, -1)
    cv2.circle(img, (128, 128), 95, 40, -1)
    cv2.ellipse(img, (100, 110), (30, 15), 30, 0, 360, 220, -1)
    cv2.ellipse(img, (156, 110), (30, 15), -30, 0, 360, 220, -1)
    cv2.rectangle(img, (115, 140), (141, 180), 120, -1)
    
    np.random.seed(42)
    noise = np.random.normal(0, 35, img.shape)
    noisy_img = np.clip(img + noise, 0, 255)
    return img, noisy_img

def quantum_rindler_diffusion(noisy_img, num_iter=20, dt=0.2, sigma=1.2, alpha=25.0, q=1.0):
    """
    Anisotropic diffusion governed by the Bogoliubov-Rindler flow.
    The deformation parameter 'q' simulates the thermodynamic chemical potential.
    When q > 1, the model strongly protects the Majorana zero-cone boundary (the edge contour)
    by heavily penalizing diffusion along the creation vector (the gradient).
    """
    u = noisy_img.copy()
    alpha_sq = alpha ** 2
    
    for iteration in range(num_iter):
        Ix = cv2.Sobel(u, cv2.CV_64F, 1, 0, ksize=3)
        Iy = cv2.Sobel(u, cv2.CV_64F, 0, 1, ksize=3)
        
        Jxx = cv2.GaussianBlur(Ix * Ix, (0, 0), sigma)
        Jyy = cv2.GaussianBlur(Iy * Iy, (0, 0), sigma)
        Jxy = cv2.GaussianBlur(Ix * Iy, (0, 0), sigma)
        
        trace = Jxx + Jyy
        det = Jxx * Jyy - Jxy * Jxy
        
        disc = np.sqrt(np.maximum(0.0, trace**2 - 4.0 * det))
        lam1 = 0.5 * (trace + disc)
        
        # Deformation parameter q introduces a thermodynamic phase shift
        # This controls the Bogoliubov mixing of the thermal dual space
        c1 = 1.0 / (1.0 + q * (lam1 / alpha_sq))
        c2 = 1.0  # Fully open diffusion in the protected null-space
        
        norm = np.sqrt(Jxy**2 + (lam1 - Jxx)**2)
        norm = np.where(norm == 0, 1e-8, norm)
        
        v1x = Jxy / norm
        v1y = (lam1 - Jxx) / norm
        
        v2x = -v1y
        v2y = v1x
        
        Dxx = c1 * (v1x * v1x) + c2 * (v2x * v2x)
        Dxy = c1 * (v1x * v1y) + c2 * (v2x * v2y)
        Dyy = c1 * (v1y * v1y) + c2 * (v2y * v2y)
        
        flux_x = Dxx * Ix + Dxy * Iy
        flux_y = Dxy * Ix + Dyy * Iy
        
        div_x = cv2.Sobel(flux_x, cv2.CV_64F, 1, 0, ksize=3)
        div_y = cv2.Sobel(flux_y, cv2.CV_64F, 0, 1, ksize=3)
        
        u += dt * (div_x + div_y)
        
    return u

if __name__ == "__main__":
    ground_truth, noisy_scan = generate_medical_phantom()
    
    # Standard diffusion (q=1.0)
    std_diffusion = quantum_rindler_diffusion(noisy_scan, num_iter=20, q=1.0)
    
    # Rindler-deformed quantum protection (q=2.5)
    rindler_diffusion = quantum_rindler_diffusion(noisy_scan, num_iter=20, q=2.5)
    
    fig, axes = plt.subplots(1, 4, figsize=(20, 5))
    
    axes[0].imshow(ground_truth, cmap='gray')
    axes[0].set_title("Ground Truth (MRI Phantom)")
    axes[0].axis('off')
    
    axes[1].imshow(noisy_scan, cmap='gray')
    axes[1].set_title("Noisy Input")
    axes[1].axis('off')
    
    axes[2].imshow(std_diffusion, cmap='gray')
    axes[2].set_title("Standard Diffusion (q=1)")
    axes[2].axis('off')
    
    axes[3].imshow(rindler_diffusion, cmap='gray')
    axes[3].set_title("Rindler Flow Protection (q=2.5)")
    axes[3].axis('off')
    
    plt.tight_layout()
    plt.savefig("quantum_rindler_flow.png")
    print("Simulation saved to quantum_rindler_flow.png")
