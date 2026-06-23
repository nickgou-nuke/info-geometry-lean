#!/usr/bin/env python3
"""
SymPy script to verify the algebraic relations of the Coriolis barrier anomaly wall:
- Drazin and Moore-Penrose projectors and their commutators with the dilation operator
- Coriolis vorticity operator skew-adjointness
- Self-concordance condition for the Itakura-Saito barrier kernel
"""

import sympy as sp

def verify_projectors_and_dilation():
    print("=== Projector and Dilation Commutator Verification ===")
    # Declare non-commutative operators
    PD = sp.Symbol('P_D', commutative=False)
    PL = sp.Symbol('P_L', commutative=False)
    PR = sp.Symbol('P_R', commutative=False)
    
    # Dilation is half-difference
    D = (PL - PR) * sp.Rational(1, 2)
    
    # Left and Right chiral boundary anomalies (commutators)
    chi_L = PD * PL - PL * PD
    chi_R = PD * PR - PR * PD
    
    # Compute [P_D, D]
    comm_PD_D = PD * D - D * PD
    
    # Decompose 1/2 * (chi_L - chi_R)
    decomp = (chi_L - chi_R) * sp.Rational(1, 2)
    
    # Subtract and expand
    diff = (comm_PD_D - decomp).expand()
    print(f"Expanded commutator difference = {diff}")
    assert diff == 0

def verify_coriolis_vorticity():
    print("=== Coriolis Vorticity Skew-Adjointness ===")
    n = 2
    # Define a general boundary generator matrix
    chi = sp.Matrix(sp.symarray('chi', (n, n)))
    # Vorticity is skew-adjoint part: 1/2 (chi - chi.T)
    vort = (chi - chi.T) * sp.Rational(1, 2)
    # Check if vort is skew-adjoint (vort.T == -vort)
    is_skew = sp.simplify(vort.T + vort).is_zero_matrix
    print(f"Is Coriolis vorticity skew-adjoint? {is_skew}")
    assert is_skew

def verify_self_concordance():
    print("=== Self-Concordant Barrier Verification ===")
    x = sp.Symbol('x', positive=True)
    # IS barrier kernel: f(x) = x - ln(x) - 1
    f = x - sp.log(x) - 1
    
    f1 = sp.diff(f, x)
    f2 = sp.diff(f1, x)
    f3 = sp.diff(f2, x)
    
    print(f"f'(x)   = {f1}")
    print(f"f''(x)  = {f2}")
    print(f"f'''(x) = {f3}")
    
    # Check self-concordance: |f'''(x)| = 2 * f''(x)**(3/2)
    # Since x > 0, f'''(x) = -2 / x^3 is negative, so |f'''(x)| = 2 / x^3
    lhs = sp.Abs(f3)
    rhs = 2 * (f2) ** sp.Rational(3, 2)
    
    diff = sp.simplify(lhs - rhs)
    print(f"Self-concordance difference |f'''| - 2 (f'')^(3/2) = {diff}")
    assert diff == 0

def main():
    verify_projectors_and_dilation()
    verify_coriolis_vorticity()
    verify_self_concordance()
    print("All SymPy formalizations verified successfully!")

if __name__ == "__main__":
    main()
