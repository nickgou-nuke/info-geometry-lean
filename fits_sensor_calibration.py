import numpy as np
import json
import os
import glob
from dataclasses import dataclass
from typing import Dict, List, Tuple

# Optional astropy for FITS handling. Assuming it's installed or we can just mock it if not present.
try:
    from astropy.io import fits
except ImportError:
    pass

def robust_median_variance(diff_array: np.ndarray) -> float:
    """Robustly compute variance from a difference image, avoiding outliers."""
    # Use Median Absolute Deviation (MAD) to estimate standard deviation
    mad = np.median(np.abs(diff_array - np.median(diff_array)))
    std_est = mad * 1.4826
    return std_est**2

def calibrate_sensor(bias_files: List[str], flat_pairs: List[Tuple[str, str]], output_json: str):
    """
    Ingest real FITS calibration stack, estimate the sensor law, and freeze parameters.
    """
    print(f"Starting FITS calibration with {len(bias_files)} bias frames and {len(flat_pairs)} flat pairs...")
    
    # 1. Process bias frames for pedestal and read noise
    bias_stack = []
    for f in bias_files:
        with fits.open(f) as hdul:
            bias_stack.append(hdul[0].data.astype(np.float64))
    
    bias_cube = np.stack(bias_stack, axis=0)
    pedestal_adu = np.median(bias_cube, axis=0)
    
    # Robust read noise variance over time axis
    read_noise_variance_adu = np.median(np.var(bias_cube, axis=0))
    
    print(f"Estimated Pedestal (median across chip): {np.median(pedestal_adu):.2f} ADU")
    print(f"Estimated Read Noise Variance: {read_noise_variance_adu:.2f} ADU^2")
    
    # 2. Process flat pairs to estimate gain and full variance law
    M_j = []
    V_j = []
    
    for f1, f2 in flat_pairs:
        with fits.open(f1) as hdul1, fits.open(f2) as hdul2:
            F1 = hdul1[0].data.astype(np.float64) - pedestal_adu
            F2 = hdul2[0].data.astype(np.float64) - pedestal_adu
            
            # Mask out saturated pixels (e.g. > 65000 ADU)
            mask = (F1 < 60000) & (F2 < 60000)
            
            if np.sum(mask) > 100:
                M = (F1[mask] + F2[mask]) / 2.0
                D = F1[mask] - F2[mask]
                
                M_j.append(np.median(M))
                V_j.append(robust_median_variance(D) / 2.0)
                
    M_j = np.array(M_j)
    V_j = np.array(V_j)
    
    # Fit the variance law V(B) = c0 + c1*B + c2*B^2
    # In ADU, V_ADU(M_ADU) = read_noise_adu + (1/G)*M_ADU + c2_adu * M_ADU^2
    # Using numpy polyfit (quadratic)
    if len(M_j) >= 3:
        coeffs = np.polyfit(M_j, V_j, deg=2)
        c2_adu, c1_adu, c0_adu = coeffs
    else:
        c2_adu = 0.0
        c1_adu = 1.0  # fallback
        c0_adu = read_noise_variance_adu
        
    gain_e_per_adu = 1.0 / c1_adu if c1_adu > 0 else 1.0
    
    print(f"Estimated Gain: {gain_e_per_adu:.3f} e-/ADU")
    
    # Convert to electron domain
    c0_e = c0_adu * (gain_e_per_adu**2)
    c1_e = c1_adu * gain_e_per_adu  # Should be exactly 1.0 ideally
    c2_e = c2_adu  # dimensionless
    
    # Export the frozen JSON calibration artifact
    calibration_artifact = {
        "gain_e_per_adu": float(gain_e_per_adu),
        "pedestal_adu": float(np.median(pedestal_adu)), # Storing scalar for simplicity, could export full array
        "read_noise_e_sq": float(c0_e),
        "variance_coefficients": {
            "c0": float(c0_e),
            "c1": float(c1_e),
            "c2": float(c2_e)
        },
        "saturation_adu": 65000,
        "bad_pixel_mask": None, 
        "temperature_range_c": None,
        "exposure_range_s": None,
        "fit_diagnostics": {
            "num_bias_frames": len(bias_files),
            "num_flat_pairs": len(flat_pairs)
        },
        "source_files": {
            "bias": bias_files,
            "flats": [list(p) for p in flat_pairs]
        }
    }
    
    with open(output_json, 'w') as f:
        json.dump(calibration_artifact, f, indent=4)
        
    print(f"Successfully saved frozen calibration artifact to {output_json}")

if __name__ == "__main__":
    # Example usage:
    # bias_files = glob.glob('data/bias_*.fits')
    # flats1 = sorted(glob.glob('data/flat_*_1.fits'))
    # flats2 = sorted(glob.glob('data/flat_*_2.fits'))
    # calibrate_sensor(bias_files, list(zip(flats1, flats2)), 'frozen_sensor_calibration.json')
    pass
