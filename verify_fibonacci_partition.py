#!/usr/bin/env python3
"""
Verify Fibonacci Scale and Primon Gas supersymmetry using SymPy.
"""
import sympy as sp

def verify_fibonacci_partition():
    print("====================================================")
    print("Verifying Fibonacci scale and partition relations...")
    
    # 1. Golden ratio definitions
    Phi = (1 + sp.sqrt(5)) / 2
    phi = (sp.sqrt(5) - 1) / 2
    
    # Verify Phi = 1 + phi
    assert sp.simplify(Phi - (1 + phi)) == 0, "Phi != 1 + phi!"
    
    # Verify Phi^2 = Phi + 1
    assert sp.simplify(Phi**2 - (Phi + 1)) == 0, "Phi^2 != Phi + 1!"
    
    # Verify 20*Phi^4 = 100 + 60*phi
    scale = 20 * Phi**4
    scale_decomp = 100 + 60 * phi
    assert sp.simplify(scale - scale_decomp) == 0, "Scale decomposition failed!"
    print("Golden ratio and Fibonacci scale decomposition verified.")
    
    # 2. Difference formula: B(x) - F(x) = x^2 * B(x)
    x = sp.Symbol('x')
    B = 1 / (1 - x)
    F = 1 + x
    diff = sp.simplify(B - F)
    expected_diff = sp.simplify(x**2 * B)
    assert diff == expected_diff, "Supersymmetry difference identity failed!"
    print("Exact partition function supersymmetry identity verified.")
    
    # 3. Numerical evaluation at beta = 137.082039
    beta = float(scale.evalf())
    print(f"Fibonacci scale beta = {beta:.6f}")
    
    # Difference for p=2 (first prime mode)
    p = 2
    x_val = p**(-beta)
    diff_val = x_val**2 / (1.0 - x_val)
    print(f"Supersymmetry difference for p=2: {diff_val:.2e}")
    # Verify it is extremely small
    assert diff_val < 1e-80, "Supersymmetry difference is too large!"
    print("Exponential suppression of non-SUSY bosonic modes verified.")
    print("====================================================")

if __name__ == "__main__":
    verify_fibonacci_partition()
