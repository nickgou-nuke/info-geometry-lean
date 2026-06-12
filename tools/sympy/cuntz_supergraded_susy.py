#!/usr/bin/env python3
"""SymPy twin for `InfoGeometry.Algebra.CuntzSupergradedSUSY`.

Checked here:
- the odd glide matrix `Q` satisfies `{Q,Q} = 2 P_x`;
- `Q` commutes with the even translation matrix `P_x`.

Not checked here:
- physical supersymmetry;
- super-Poincare representation theory;
- a full Cuntz-algebra Hilbert-space supercharge.
"""

import sympy as sp

def verify_cuntz_susy_algebra():
    # Q: odd finite generator, represented by the glide reflection.
    Q = sp.Matrix([
        [1,  0, sp.Rational(1, 2)],
        [0, -1, 0],
        [0,  0, 1]
    ])
    
    # P_x: even finite generator, represented by pure translation.
    P_x = sp.Matrix([
        [1, 0, 1],
        [0, 1, 0],
        [0, 0, 1]
    ])
    
    # 1. The SUSY Anti-Commutator Relation: {Q, Q} = Q*Q + Q*Q
    anti_commutator_QQ = Q * Q + Q * Q
    
    susy_momentum = 2 * P_x
    is_susy_generator = (anti_commutator_QQ == susy_momentum)
    
    # 2. SUSY Conservation Law: The Supercharge commutes with Momentum: [Q, P_x] = 0
    commutator_QP = Q * P_x - P_x * Q
    is_conserved = (commutator_QP == sp.zeros(3, 3))
    
    print("=== Finite supergraded wallpaper algebra ===")
    print(f"Odd glide generator Q:\n{Q}")
    print(f"Even translation generator P_x:\n{P_x}")
    print(f"\nSelf-anticommutator {{Q, Q}} == 2 P_x:")
    print(f"{anti_commutator_QQ} == {susy_momentum} -> {is_susy_generator}")
    print(f"\nFinite commutator [Q, P_x] == 0:")
    print(f"{commutator_QP} == 0 -> {is_conserved}")
    
    if is_susy_generator and is_conserved:
        print("\n[SUCCESS] finite supergraded wallpaper algebra verified.")

if __name__ == "__main__":
    verify_cuntz_susy_algebra()
