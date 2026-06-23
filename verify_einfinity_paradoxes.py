#!/usr/bin/env python3
"""
Verify E-infinity quantum paradoxes and energy division using SymPy.
"""
import sympy as sp

def verify_einfinity():
    print("====================================================")
    print("Verifying E-infinity quantum paradox relations...")
    
    # 1. Lower golden ratio φ = (√5 - 1) / 2
    phi = (sp.sqrt(5) - 1) / 2
    
    # Verify φ^2 + φ = 1
    assert sp.simplify(phi**2 + phi - 1) == 0, "phi^2 + phi != 1!"
    
    # Verify the energy partition identity: φ^5 + 5*φ^2 = 2
    assert sp.simplify(phi**5 + 5*phi**2 - 2) == 0, "phi^5 + 5*phi**2 != 2!"
    print("Golden ratio power relations verified successfully.")

    # Verify the polynomial factorization Q(x) = chi(x) * P_quot(x)
    x_sym = sp.Symbol('x')
    Q_poly = x_sym**5 + 5*x_sym**2 - 2
    chi_poly = x_sym**2 + x_sym - 1
    P_quot_poly = x_sym**3 - x_sym**2 + 2*x_sym + 2
    assert sp.simplify(Q_poly - chi_poly * P_quot_poly) == 0, "Factorization failed!"
    print("Polynomial factorization Q(x) = chi(x) * P_quot(x) verified.")
    
    # 2. Evaluate quantities numerically
    Hardy_E = float(phi**5)
    e_ord = float(phi**5 / 2)
    e_dark = float(5 * phi**2 / 2)
    
    print(f"Hardy's quantum entanglement probability φ^5 = {Hardy_E:.6f} (≈ 9.0%)")
    print(f"Ordinary energy fraction φ^5 / 2 = {e_ord*100:.2f}% (≈ 4.5%)")
    print(f"Dark energy fraction 5*φ^2 / 2 = {e_dark*100:.2f}% (≈ 95.5%)")
    print(f"Total energy fraction sum: {(e_ord + e_dark)*100:.2f}% (== 100%)")
    
    assert abs((e_ord + e_dark) - 1.0) < 1e-10, "Energy conservation check failed!"
    print("E-infinity energy division and conservation verified successfully.")
    
    # 3. Verify Cantorian spacetime dimension relation (1 + phi)^3 = 4 + phi^3
    assert sp.simplify((1 + phi)**3 - phi**3 - 4) == 0, "Cantorian dimension relation failed!"
    print("SymPy: Cantorian dimension identity (1 + phi)^3 = 4 + phi^3 verified.")
    
    # 4. Verify rational approximations
    assert abs(Hardy_E / 2 - 1/22) < 0.001, "Ordinary energy rational approx failed!"
    assert abs(e_dark - 21/22) < 0.001, "Dark energy rational approx failed!"
    print("SymPy: Rational approximations (1/22, 21/22) verified successfully.")
    
    # 5. Verify Carlos Castro's second relation (hep-th/0203086)
    castro_LHS = 1 + (1+phi)**2 + (1+phi)**4 + (1+phi)**8 + (1+phi)**3 + (1+phi)**9
    assert sp.simplify(castro_LHS - (100 + 61*phi)) == 0, "Carlos Castro's second relation failed!"
    print("SymPy: Carlos Castro's second relation verified successfully.")
    print("====================================================")

if __name__ == "__main__":
    verify_einfinity()
