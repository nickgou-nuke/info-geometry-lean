import numpy as np
import time
import sys
import os

try:
    from astropy.io import fits
    import astroscrappy
    ASTROSCRAPPY_AVAILABLE = True
except ImportError:
    ASTROSCRAPPY_AVAILABLE = False

# Import our custom Bregman Oracle
from python_oracle import CmosEstimatorOracle

def detect_cosmics_bregman_streaming(image_stack, c0=10.0, c1=0.5, c2=0.01):
    """
    Drop-in replacement for processing image stacks using the Bregman Oracle.
    Unlike standard LA Cosmic which does expensive spatial convolutions per frame,
    this updates an O(1) temporal state recursively.
    
    Returns:
        clean_stack (np.ndarray): The cosmic-ray cleaned image stack
        crmask_stack (np.ndarray): The boolean mask of cosmic rays over time
    """
    T, H, W = image_stack.shape
    oracle = CmosEstimatorOracle(
        c0=c0, c1=c1, c2=c2,
        pi_G=0.333, pi_P=0.333, pi_I=0.334,
        T_beta=1.0, rho=0.99, rho_C=0.95,
        c_t=20.0, eps_t=2.0,
        shape=(H, W)
    )
    
    clean_stack = np.zeros_like(image_stack, dtype=np.float64)
    crmask_stack = np.zeros_like(image_stack, dtype=bool)
    
    for t in range(T):
        # Update oracle with the current frame
        clean_frame, crmask = oracle.update(image_stack[t])
        
        crmask_stack[t] = crmask
        
        # Where there is a cosmic ray, substitute the clean background estimate
        clean_stack[t] = np.where(crmask, clean_frame, image_stack[t])
        
    return clean_stack, crmask_stack

def benchmark_against_lacosmic(fits_path):
    print(f"Loading test FITS file: {fits_path}")
    with fits.open(fits_path) as hdul:
        base_image = hdul[0].data.astype(np.float64)
        
    # Standardize image size for benchmarking to a manageable patch if it's too big
    # Let's just use the full image for a real benchmark
    H, W = base_image.shape
    T = 20  # Simulate 20 consecutive frames of the same field
    
    print(f"Simulating a {T}-frame stream for a {H}x{W} sensor...")
    
    # Generate synthetic stack from base image
    np.random.seed(42)
    # Add varying read noise and Poisson noise
    image_stack = np.zeros((T, H, W))
    for t in range(T):
        read_noise = np.random.normal(0, 10, (H, W))
        # Add Poisson noise approximation
        image_stack[t] = base_image + read_noise + np.random.normal(0, np.sqrt(np.clip(base_image, 1, None)))
        
    # Inject cosmic ray spikes
    cr_pixels = [(5, 50, 50), (10, 100, 100), (15, 200, 200)]
    for (t, y, x) in cr_pixels:
        image_stack[t, y, x] += 10000.0  # Massive spike
        
    print("\n--- Running Astroscrappy (Standard L.A. Cosmic) ---")
    start_time = time.time()
    lacosmic_mask = np.zeros((T, H, W), dtype=bool)
    for t in range(T):
        # LA Cosmic operates frame-by-frame independently
        crmask, _ = astroscrappy.detect_cosmics(image_stack[t], sigclip=4.5, sigfrac=0.3, objlim=5.0)
        lacosmic_mask[t] = crmask
    lacosmic_time = time.time() - start_time
    print(f"LA Cosmic Time: {lacosmic_time:.2f} seconds")
    
    print("\n--- Running Bregman Stream Oracle (Our Method) ---")
    start_time = time.time()
    _, bregman_mask = detect_cosmics_bregman_streaming(image_stack)
    bregman_time = time.time() - start_time
    print(f"Bregman Oracle Time: {bregman_time:.2f} seconds")
    
    print("\n--- Benchmark Summary ---")
    speedup = lacosmic_time / bregman_time
    print(f"Speedup: {speedup:.2f}x faster")
    
    # Check if we caught the CRs
    print("Cosmic Ray Detection Check (True Positives):")
    for (t, y, x) in cr_pixels:
        la_caught = lacosmic_mask[t, y, x]
        br_caught = bregman_mask[t, y, x]
        print(f"  Spike at t={t}, ({y},{x}) -> LA Cosmic: {la_caught} | Bregman: {br_caught}")

if __name__ == "__main__":
    fits_file = "astroscrappy/astroscrappy/tests/data/gmos.fits"
    if not os.path.exists(fits_file):
        print(f"Error: Could not find {fits_file}")
    elif not ASTROSCRAPPY_AVAILABLE:
        print("Error: astropy and astroscrappy are required. Please install them to run the benchmark.")
    else:
        benchmark_against_lacosmic(fits_file)
