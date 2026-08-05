import numpy as np
from python_cmos_sim import ModularMoebiusCMOSPipeline

def main():
    B = 200.0
    sigma = 14.45
    variance = sigma**2
    
    # We set noise_floor to 8.8 so that V(B) = B + noise_floor = 208.8 approx sigma^2
    noise_floor = 8.8
    
    params = {
        'gain': 1.0,
        'pedestal': 0.0,
        'read_noise_e_sq': noise_floor,
        'quantization_noise_e_sq': 0.0,
        'variance_floor': 1.0,
        'log_argument_floor': 1e-10,
        # 'hardware_low_signal_cut': 84.95, # Disabled for mathematical domain test
        'rho': 0.99,
        'mu_admission': 37.90,
        'epsilon_admission': 3.23,
        'tau_cosmic': 31.56,
        'epsilon_cosmic': 2.88,
        'tau_dropout': 62.57,
        'epsilon_dropout': 1.71,
        'k_l_admission': 0.01,
        'k_l_cosmic': 0.00,
        'k_l_dropout': 0.01,
        'responsibility_cut': 0.01,
        'cosmic_probability_cut': 0.5,
        'dropout_probability_cut': 0.5,
    }
    
    pipe = ModularMoebiusCMOSPipeline((1, 1), params)
    
    print(f"{'h (sigma)':<10} | {'X_h':<10} | {'aX+b':<10} | {'Valid?':<10} | {'Recall_drop':<15} | {'DomainFaultRate':<15} | {'OverallDetectionRate':<20}")
    print("-" * 105)
    
    h_vals = [1, 2, 3, 5, 7, 10, 12, 14, 15, 20]
    for h in h_vals:
        X_h = B - h * sigma
        arg_X = X_h + noise_floor
        
        # We need a large number of frames to get rates, or since it's deterministic for a single pixel:
        # Actually it's 1 pixel so rates are 0 or 1.
        
        # Init background
        pipe.B = np.array([[B]], dtype=np.float32)
        pipe.is_initialized = True
        
        X_adu = np.array([[X_h]], dtype=np.float32)
        _, state, probs = pipe.process_frame(X_adu)
        
        is_valid = 1 if arg_X > params['log_argument_floor'] else 0
        p_drop = probs.get('p_drop', np.zeros((1,1)))[0, 0]
        
        # Hard classes
        s = state[0, 0]
        domain_fault = 1 if s == 3 else 0
        is_dropout = 1 if s == 2 else 0
        
        recall_drop = is_dropout if is_valid else "N/A"
        overall_det = 1 if (is_dropout or domain_fault) else 0
        
        print(f"{h:<10} | {X_h:<10.2f} | {arg_X:<10.2f} | {is_valid:<10} | {str(recall_drop):<15} | {domain_fault:<15} | {overall_det:<20}")

if __name__ == '__main__':
    main()
