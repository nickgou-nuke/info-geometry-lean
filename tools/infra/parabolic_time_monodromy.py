#!/usr/bin/env python3
"""
Parabolic nilpotent-flow verification.

This script checks a bounded algebraic packet:

- a concrete 2×2 generator is nilpotent,
- its affine flow U(t) = I + tK is unipotent,
- trace(U(t)) = 2 and det(U(t)) = 1.

It does not prove the global physical statement “Time = Modular Flow = de Rham
Monodromy”.  It only supports the local nilpotent/parabolic matrix lane used by
the theorem-honest Lean files.

References:
- Connes-Rovelli thermal time hypothesis
- Tomita-Takesaki modular theory
- info-geometry-lean: ModularMonodromyClock.lean
"""

import sympy as sp
from typing import Tuple, Optional


def nilpotent_generator(a: sp.Symbol, b: sp.Symbol) -> sp.Matrix:
    """
    Construct a generic nilpotent matrix K in M₂(ℂ) parameterized by (a, b).
    
    This matrix satisfies:
    - K² = 0 (nilpotent of order 2)
    - det(K) = 0 (lies on the forbidden light cone)
    - Tr(K) = 0 (traceless, pure derivation)
    
    The parameterization K = [[ab, -a²], [b², -ab]] represents the most general
    2×2 nilpotent matrix up to similarity.
    
    Args:
        a, b: Complex parameters defining the null direction
        
    Returns:
        A 2×2 nilpotent matrix K with K² = 0
    """
    K = sp.Matrix([[a*b, -a**2], [b**2, -a*b]])
    return K


def verify_nilpotency(K: sp.Matrix) -> sp.Matrix:
    """
    Verify that K is nilpotent (K² = 0).
    
    Args:
        K: The matrix to test
        
    Returns:
        K² (should simplify to the zero matrix)
    """
    return sp.simplify(K * K)


def modular_flow(K: sp.Matrix, t: sp.Symbol) -> sp.Matrix:
    """
    Compute the modular automorphism flow U(t) = exp(tK).
    
    Since K² = 0, the exponential series terminates:
    exp(tK) = I + tK + (tK)²/2! + ... = I + tK
    
    This is the parabolic shear transformation.
    
    Args:
        K: Nilpotent generator (K² = 0)
        t: Real time parameter
        
    Returns:
        U(t) = I + tK (exact, no series expansion needed)
    """
    I = sp.eye(K.shape[0])
    U_t = I + t * K
    return sp.simplify(U_t)


def classify_transformation(U: sp.Matrix) -> Tuple[sp.Expr, sp.Expr, str]:
    """
    Classify the transformation U by its trace and determinant.
    
    For 2×2 matrices over ℂ:
    - Trace = 2, Det = 1 → Parabolic (shear transformation)
    - |Trace| > 2 → Hyperbolic (Lorentz boost)
    - |Trace| < 2 → Elliptic (rotation)
    
    Args:
        U: 2×2 transformation matrix
        
    Returns:
        Tuple of (trace, determinant, classification string)
    """
    trace_U = sp.simplify(U.trace())
    det_U = sp.simplify(U.det())
    
    # Classification logic
    if trace_U == 2 and det_U == 1:
        classification = "PARABOLIC (shear transformation)"
    elif trace_U.is_real:
        # For real trace, check magnitude
        classification = "Requires numeric evaluation"
    else:
        classification = "General linear transformation"
    
    return trace_U, det_U, classification


def run_parabolic_time_verification() -> None:
    """
    Execute the full verification pipeline and print results.
    
    This demonstrates that:
    1. The null cone generator K is nilpotent (K² = 0)
    2. The modular flow U(t) = exp(tK) = I + tK is unipotent
    3. U(t) is a parabolic shear (Trace = 2, Det = 1)
    4. (U(t) - I)² = 0
    """
    print("=" * 70)
    print("SYMPY: THE PARABOLIC TIME CLOCK & NULL CONE MONODROMY")
    print("=" * 70)
    
    # 1. Define parameters and construct the null cone generator
    a, b = sp.symbols('a b', complex=True)
    K = nilpotent_generator(a, b)
    
    print("\n1. Modular Hamiltonian / Null Cone Generator K:")
    sp.pprint(K)
    print(f"   Determinant(K): {K.det()} (must be 0 on forbidden cone)")
    print(f"   Trace(K):       {K.trace()} (must be 0 for pure derivation)")
    
    # 2. Verify nilpotency
    K_sq = verify_nilpotency(K)
    print("\n2. Nilpotency Check (K² = 0 implies strict null projection):")
    sp.pprint(K_sq)
    assert K_sq == sp.zeros(2), "K must be nilpotent!"
    print("   ✓ K² = 0 confirmed")
    
    # 3. Compute the modular flow
    t = sp.Symbol('t', real=True)
    U_t = modular_flow(K, t)
    
    print("\n3. Modular Automorphism Flow U(t) = exp(tK) = I + tK:")
    sp.pprint(U_t)
    
    # 4. Topological classification
    trace_U, det_U, classification = classify_transformation(U_t)
    
    print("\n4. Topological Classification of the Time Clock:")
    print(f"   Trace(U(t)): {trace_U}")
    print(f"   Det(U(t)):   {det_U}")
    print(f"   Type:        {classification}")
    
    # 5. Verify unipotency: (U(t) - I)² = 0
    U_minus_I = U_t - sp.eye(2)
    U_minus_I_sq = sp.simplify(U_minus_I * U_minus_I)
    print("\n5. Unipotency Check ((U(t) - I)² = 0):")
    sp.pprint(U_minus_I_sq)
    assert U_minus_I_sq == sp.zeros(2), "U(t) must be unipotent!"
    print("   ✓ (U(t) - I)² = 0 confirmed")
    
    # 6. Physical interpretation
    print("\n" + "=" * 70)
    print("CONCLUSION:")
    print("=" * 70)
    print("The exponential flow of the null cone generator acts as a")
    print("PARABOLIC clock. It shears the state space without scaling it,")
    print("matching the light-like (null) translations of the Minkowski boundary.")
    print()
    print("This verifies the local SymPy nilpotent/parabolic packet:")
    print("  exp(tK) = I + tK for the chosen square-zero generator")
    print("  exp(tK) is unipotent and parabolic (trace 2, determinant 1)")
    print("No global de Rham/modular/time identification is claimed here.")
    print("=" * 70)


def explicit_numeric_example() -> None:
    """
    Provide a concrete numeric example with specific (a, b) values.
    
    This gives an explicit matrix representation for intuition.
    """
    print("\n" + "=" * 70)
    print("EXPLICIT NUMERIC EXAMPLE (a=1, b=1):")
    print("=" * 70)
    
    K = nilpotent_generator(sp.Integer(1), sp.Integer(1))
    print("\nNull cone generator K:")
    sp.pprint(K)
    
    t = sp.Symbol('t', real=True)
    U_t = modular_flow(K, t)
    print("\nFlow U(t) = I + tK:")
    sp.pprint(U_t)
    
    # Evaluate at specific times
    for t_val in [0, 1, 2, sp.Rational(1, 2)]:
        U_eval = U_t.subs(t, t_val)
        print(f"\nU(t={t_val}):")
        sp.pprint(U_eval)
        trace_U, det_U, _ = classify_transformation(U_eval)
        print(f"  Trace: {trace_U}, Det: {det_U}")


if __name__ == "__main__":
    run_parabolic_time_verification()
    explicit_numeric_example()
    
    print("\n" + "=" * 70)
    print("VERIFICATION COMPLETE")
    print("=" * 70)
    print(f"Lean counterpart: lean/InfoGeometry/Canonical/ModularMonodromyClock.lean")
    print(f"Key theorems:")
    print(f"  - parabolicTimeClock")
    print(f"  - modularFlow_nilpotent_generator")
    print(f"  - deRhamResidue_nilpotent")
    print("=" * 70)