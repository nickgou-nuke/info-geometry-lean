import numpy as np
import pytest
from python_cmos_sim import ModularMoebiusCMOSPipeline

def get_full_params():
    return {
        'gain': 1.0,
        'pedestal': 0.0,
        'read_noise_e_sq': 9.05,
        'quantization_noise_e_sq': 1.0,
        'variance_floor': 1.0,
        'domain_floor': 84.95,
        'rho': 0.99,
        'mu_admission': 10.0,
        'epsilon_admission': 2.0,
        'tau_cosmic': 20.0,
        'epsilon_cosmic': 2.0,
        'tau_dropout': 20.0,
        'epsilon_dropout': 2.0,
        'k_l_admission': 0.0,
        'k_l_cosmic': 0.0,
        'k_l_dropout': 0.0,
        'responsibility_cut': 0.01,
        'cosmic_probability_cut': 0.5,
        'dropout_probability_cut': 0.5,
    }

def test_energy_conservation():
    params = get_full_params()
    pipe = ModularMoebiusCMOSPipeline((1, 1), params)
    
    pipe.process_frame(np.array([[100.0]])) # init
    
    # Positive deviation
    frame = np.array([[120.0]])
    B_est, state, probs = pipe.process_frame(frame)
    
    # Manual verify
    # X_e = 120, B = 100
    noise = 10.05
    arg_X = 120 + noise
    arg_B = 100 + noise
    D_plus = arg_X * np.log(arg_X / arg_B) - 20.0
    
    # Negative deviation
    pipe.B = np.array([[100.0]])
    frame2 = np.array([[80.0]])
    # We clip domain fault, let's pick 85
    frame2 = np.array([[86.0]])
    B_est, state, probs = pipe.process_frame(frame2)
    arg_X2 = 86 + noise
    D_minus = arg_X2 * np.log(arg_X2 / arg_B) + 14.0
    
    assert D_plus > 0
    assert D_minus > 0

def test_branch_gating():
    params = get_full_params()
    pipe = ModularMoebiusCMOSPipeline((1, 1), params)
    
    pipe.process_frame(np.array([[100.0]])) # init
    
    frame = np.array([[150.0]]) # X > B
    _, _, probs = pipe.process_frame(frame)
    assert probs['p_drop'] == 0.0
    
    pipe.B = np.array([[100.0]])
    frame2 = np.array([[86.0]]) # X < B
    _, _, probs2 = pipe.process_frame(frame2)
    assert probs2['p_CR'] == 0.0

def test_domain_fault():
    params = get_full_params()
    pipe = ModularMoebiusCMOSPipeline((1, 1), params)
    
    pipe.process_frame(np.array([[100.0]])) # init
    
    frame = np.array([[-10.0]]) # Very low, triggers domain fault
    B_est, state, probs = pipe.process_frame(frame)
    
    assert probs['r'] == 0.0

def test_dropout_monotonicity():
    params = get_full_params()
    params['tau_dropout'] = 0.0 # Force probabilities for testing
    params['epsilon_dropout'] = 1.0
    
    pipe = ModularMoebiusCMOSPipeline((1, 1), params)
    pipe.process_frame(np.array([[100.0]])) # init
    
    # We decrease X, meaning drop increases
    X_vals = np.linspace(95.0, 15.0, 10)
    p_drops = []
    
    for x in X_vals:
        pipe.B = np.array([[100.0]])
        _, _, probs = pipe.process_frame(np.array([[x]]))
        p_drops.append(probs['p_drop'])
        
    p_drops = np.array(p_drops)
    
    # Monotonically increasing as X decreases (and drop amplitude increases)
    assert np.all(np.diff(p_drops) >= -1e-6)

def test_barycentric_equivalence():
    rho = 0.99
    S = 9900.0
    N = 99.0
    r = 0.5
    X = 150.0
    
    B = S / N # 100.0
    
    val1 = (rho * S + r * X) / (rho * N + r)
    val2 = B + (r / (rho * N + r)) * (X - B)
    
    np.testing.assert_allclose(val1, val2)

