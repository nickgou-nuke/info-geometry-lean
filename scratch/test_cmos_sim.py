import numpy as np
import matplotlib.pyplot as plt
from python_cmos_sim import ModularMoebiusCMOSPipeline, PixelClass

def generate_track(shape, Q, L, phi, w, x0, y0):
    """Generates a synthetic cosmic ray track."""
    y, x = np.ogrid[0:shape[0], 0:shape[1]]
    
    # Direction vectors
    dir_x = np.cos(phi)
    dir_y = np.sin(phi)
    
    # Perpendicular and parallel distances
    d_parallel = (x - x0) * dir_x + (y - y0) * dir_y
    d_perp = (x - x0) * -dir_y + (y - y0) * dir_x
    
    # Gaussian transverse profile with box longitudinal profile
    C_p = np.exp(-(d_perp**2) / (2 * w**2)) * (np.abs(d_parallel) <= L / 2)
    
    sum_C = np.sum(C_p)
    if sum_C > 0:
        return Q * (C_p / sum_C)
    return np.zeros(shape, dtype=np.float32)

def generate_synthetic_data(shape=(100, 100), num_frames=50):
    # Base latent background
    B_star = np.ones(shape, dtype=np.float32) * 500.0
    sigma_R = 3.16  # read noise stddev (so variance is 10)
    
    frames = []
    cosmic_ground_truth = []
    dropout_ground_truth = []
    domain_fault_truth = []
    
    for t in range(num_frames):
        # 4.1 Background generator (Poisson + Gaussian read noise)
        shot_noise = np.random.poisson(B_star).astype(np.float32)
        read_noise = np.random.normal(0, sigma_R, size=shape).astype(np.float32)
        frame = shot_noise + read_noise
        
        cr_mask = np.zeros(shape, dtype=bool)
        do_mask = np.zeros(shape, dtype=bool)
        df_mask = np.zeros(shape, dtype=bool)
        
        # 4.2 Cosmic-ray injection (Tracks)
        if t % 10 == 5:
            # Inject a track
            track = generate_track(shape, Q=15000.0, L=15.0, phi=np.pi/4, w=0.8, x0=50.0, y0=50.0)
            frame += track
            cr_mask = track > 100.0 # significant hit mask
            
        # 4.3 Dropout injection (Deep negative perturbations)
        if t % 20 == 10:
            # Drop a cluster
            do_y, do_x = np.ogrid[-2:3, -2:3]
            mask = (do_x**2 + do_y**2 <= 4)
            y0, x0 = 20, 80
            frame[y0-2:y0+3, x0-2:x0+3][mask] -= 450.0
            do_mask[y0-2:y0+3, x0-2:x0+3][mask] = True
            
        # 4.4 Domain-failure injection
        if t == 40:
            # Hard invalid domain (<= 0 after adding noise_floor)
            # noise_floor is around 11
            frame[80, 20] = -500.0
            df_mask[80, 20] = True
            
        frames.append(frame)
        cosmic_ground_truth.append(cr_mask)
        dropout_ground_truth.append(do_mask)
        domain_fault_truth.append(df_mask)
        
    return B_star, frames, cosmic_ground_truth, dropout_ground_truth, domain_fault_truth

def main():
    shape = (100, 100)
    B_star, frames, cr_truth, do_truth, df_truth = generate_synthetic_data(shape, 50)
    
    params = {
        'gain': 1.0,
        'pedestal': 0.0,
        'read_noise_e_sq': 10.0,
        'quantization_noise_e_sq': 1.0,
        'variance_floor': 1.0,
        
        'k_l_admission': 1.0,
        'k_l_cosmic': 2.0,
        'k_l_dropout': 2.0,
        
        'mu_admission': 20.0,
        'epsilon_admission': 2.0,
        
        'tau_cosmic': 25.0,
        'epsilon_cosmic': 1.0,
        
        'tau_dropout': 15.0,
        'epsilon_dropout': 1.0,
        
        'responsibility_cut': 0.01,
        'cosmic_probability_cut': 0.5,
        'dropout_probability_cut': 0.5,
        'rho': 0.99
    }
    
    pipeline = ModularMoebiusCMOSPipeline(shape, params)
    
    print("Testing 5-way branch strict classification and domain failure masking...")
    for i, frame in enumerate(frames):
        X_adu = frame
        B, state, probs = pipeline.process_frame(X_adu)
        
        # Test property 1: domain fault forces p = 0
        if np.any(df_truth[i]):
            idx = tuple(np.argwhere(df_truth[i])[0])
            print(f"\\nFrame {i} - Domain Fault Injected at {idx}:")
            print(f"  Signal: {frame[idx]:.1f}")
            print(f"  State: {PixelClass(state[idx]).name}")
            print(f"  Probabilities -> CR: {probs['p_CR'][idx]:.3f}, Drop: {probs['p_drop'][idx]:.3f}, Adm: {probs['r'][idx]:.3f}")
            
            assert probs['p_CR'][idx] == 0.0
            assert probs['p_drop'][idx] == 0.0
            assert probs['r'][idx] == 0.0
            assert state[idx] == PixelClass.DOMAIN_FAULT

        if np.any(cr_truth[i]):
            idx = tuple(np.argwhere(cr_truth[i])[10]) # arbitrary point on track
            if i == 5:
                print(f"\\nFrame {i} - Cosmic Track Injected:")
                print(f"  Track sample at {idx} - Signal: {frame[idx]:.1f}")
                print(f"  State: {PixelClass(state[idx]).name}")
                
                # Check negative gating on positive branch
                assert probs['p_drop'][idx] == 0.0
                assert state[idx] == PixelClass.COSMIC
                
        if np.any(do_truth[i]):
            idx = tuple(np.argwhere(do_truth[i])[0])
            if i == 10:
                print(f"\\nFrame {i} - Dropout Injected:")
                print(f"  Dropout sample at {idx} - Signal: {frame[idx]:.1f}")
                print(f"  State: {PixelClass(state[idx]).name}")
                
                # Check positive gating on negative branch
                assert probs['p_CR'][idx] == 0.0
                assert state[idx] == PixelClass.DROPOUT

    print("\\nProperty tests passed successfully!")

if __name__ == "__main__":
    main()
