import numpy as np
import json
import os
try:
    from astropy.io import fits
except ImportError:
    fits = None

def generate_mock_calibration_fits(output_dir="mock_fits"):
    """Generates mock bias and flat frames to simulate a real FITS calibration stack."""
    if not os.path.exists(output_dir):
        os.makedirs(output_dir)
        
    shape = (100, 100)
    true_pedestal = 100.0
    true_read_noise_adu = 3.0
    true_gain = 1.2 # e-/ADU
    
    bias_files = []
    flat_files = []
    
    print("Generating mock bias frames...")
    for i in range(20):
        bias = np.random.normal(true_pedestal, true_read_noise_adu, size=shape).astype(np.float32)
        hdu = fits.PrimaryHDU(bias)
        hdu.header['EXPTIME'] = 0.0
        hdu.header['CCD-TEMP'] = -20.0
        fname = os.path.join(output_dir, f"bias_{i}.fits")
        hdu.writeto(fname, overwrite=True)
        bias_files.append(fname)
        
    print("Generating mock flat frames...")
    # Flat field variations
    y, x = np.mgrid[0:shape[0], 0:shape[1]]
    P_p = 1.0 + 0.1 * np.sin(x/10) * np.cos(y/10)
    
    for level, signal_e in enumerate([500, 2000, 8000]):
        for i in range(2): # Pair for variance estimation
            shot_e = np.random.poisson(P_p * signal_e).astype(np.float32)
            read_e = np.random.normal(0, true_read_noise_adu * true_gain, size=shape)
            total_e = shot_e + read_e
            
            adu = (total_e / true_gain) + true_pedestal
            adu = np.clip(adu, 0, 65535).astype(np.float32)
            
            hdu = fits.PrimaryHDU(adu)
            hdu.header['EXPTIME'] = float(level + 1)
            hdu.header['CCD-TEMP'] = -20.0
            fname = os.path.join(output_dir, f"flat_{level}_{i}.fits")
            hdu.writeto(fname, overwrite=True)
            flat_files.append(fname)
            
    return bias_files, flat_files

def extract_sensor_calibration(bias_files, flat_files):
    print("Extracting pedestal and read noise from bias frames...")
    bias_stack = [fits.getdata(f) for f in bias_files]
    bias_cube = np.stack(bias_stack, axis=0)
    
    pedestal_map = np.median(bias_cube, axis=0)
    
    # Calculate read noise variance using consecutive pairs
    var_adu_list = []
    for i in range(0, len(bias_files)-1, 2):
        diff = bias_cube[i] - bias_cube[i+1]
        var_adu_list.append(0.5 * np.var(diff))
    
    read_noise_sq_adu = np.mean(var_adu_list)
    print(f"Estimated Pedestal: {np.mean(pedestal_map):.2f} ADU")
    print(f"Estimated Read Noise Var (ADU): {read_noise_sq_adu:.2f} ADU^2")
    
    print("Extracting gain from flat pairs (Photon Transfer Curve)...")
    means = []
    variances = []
    for i in range(0, len(flat_files), 2):
        F1 = fits.getdata(flat_files[i]) - pedestal_map
        F2 = fits.getdata(flat_files[i+1]) - pedestal_map
        
        M_j = (F1 + F2) / 2.0
        D_j = F1 - F2
        
        V_j = 0.5 * np.var(D_j)
        means.append(np.mean(M_j))
        variances.append(V_j)
        
    means = np.array(means)
    variances = np.array(variances)
    
    # V_ADU = B_ADU / G + sigma_R_ADU^2
    # Fit line V = m * M + c
    m, c = np.polyfit(means, variances, 1)
    gain = 1.0 / m
    print(f"Estimated Gain: {gain:.3f} e-/ADU")
    
    read_noise_e_sq = gain**2 * read_noise_sq_adu
    
    calibration_artifact = {
        "gain_e_per_adu": float(gain),
        "pedestal_adu": float(np.mean(pedestal_map)),
        "read_noise_e_sq": float(read_noise_e_sq),
        "variance_coefficients": {
            "c0": float(read_noise_e_sq),
            "c1": 1.0, # Pure Poisson
            "c2": 0.0
        },
        "saturation_adu": 65535,
        "bad_pixel_mask": None,
        "temperature_range_c": [-20.0, -20.0],
        "exposure_range_s": [0.0, 3.0],
        "fit_diagnostics": {
            "ptc_slope": float(m),
            "ptc_intercept": float(c)
        },
        "source_files": bias_files + flat_files
    }
    
    with open("calibration_artifact.json", "w") as f:
        json.dump(calibration_artifact, f, indent=4)
        
    print("Saved calibration artifact to calibration_artifact.json")

if __name__ == "__main__":
    if fits is None:
        print("Please install astropy: pip install astropy")
    else:
        biases, flats = generate_mock_calibration_fits()
        extract_sensor_calibration(biases, flats)
