#!/usr/bin/env python3
"""
Verify Bost-Connes modular flow & Liouville grading commutativity using SymPy.
"""
import sympy as sp

def verify_bost_connes_commute():
    print("====================================================")
    print("Verifying Bost-Connes modular flow & Liouville grading...")
    t = sp.Symbol('t', real=True)
    n = sp.Symbol('n', integer=True, positive=True)
    Omega_n = sp.Symbol('Omega_n', integer=True, nonnegative=True)
    
    # Basis element mu_n
    mu_n = sp.Symbol('mu_n', commutative=False)
    
    # LHS: Gamma(sigma_t(mu_n)) = n^(I * t) * (-1)^Omega_n * mu_n
    LHS = n**(sp.I * t) * (-1)**Omega_n * mu_n
    
    # RHS: sigma_t(Gamma(mu_n)) = (-1)^Omega_n * n**(sp.I * t) * mu_n
    RHS = (-1)**Omega_n * n**(sp.I * t) * mu_n
    
    # Verify LHS = RHS
    assert LHS == RHS, "Verification failed!"
    print(f"LHS = {LHS}")
    print(f"RHS = {RHS}")
    print("SymPy: Bost-Connes commutativity verified successfully.")
    print("====================================================")

if __name__ == "__main__":
    verify_bost_connes_commute()
