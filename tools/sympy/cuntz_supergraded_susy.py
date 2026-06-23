#!/usr/bin/env python3
"""SymPy twin for `InfoGeometry.Algebra.CuntzSupergradedSUSY`.

Checked here:
- the odd glide matrix `Q` satisfies `{Q,Q} = 2 P_x`, matching Lean theorem
  `wallpaper_generates_SUSY`;
- `Q` commutes with the even translation matrix `P_x`.
- the formal Cuntz parity map `Pi(S_i)=-S_i`, `Pi(S_i^dag)=-S_i^dag`
  preserves the algebraic Cuntz relations and makes `Q_i=S_i+S_i^dag`
  odd while `Q_i^2` is even.

Not checked here:
- physical supersymmetry;
- super-Poincare representation theory;
- a full Cuntz-algebra Hilbert-space supercharge.
"""

import sympy as sp


def verify_cuntz_parity_algebra(n=3):
    S = sp.symbols(f"S0:{n}", commutative=False)
    Sd = sp.symbols(f"Sd0:{n}", commutative=False)

    def pi(expr):
        out = expr
        for s, sd in zip(S, Sd):
            out = out.subs({s: -s, sd: -sd}, simultaneous=True)
        return sp.expand(out)

    for i in range(n):
        for j in range(n):
            relation_lhs = Sd[i] * S[j]
            relation_rhs = sp.Integer(1) if i == j else sp.Integer(0)
            assert pi(relation_lhs) == relation_lhs
            assert pi(relation_rhs) == relation_rhs

    range_sum = sum(S[i] * Sd[i] for i in range(n))
    assert pi(range_sum) == range_sum

    Q = S[0] + Sd[0]
    P = Q * Q
    assert sp.expand(pi(Q) + Q) == 0
    assert sp.expand(pi(P) - P) == 0

    print("=== Formal Cuntz parity algebra ===")
    print(f"Pi preserves S_i^dag S_j and sum_i S_i S_i^dag for n={n}")
    print("Pi(Q_i) = -Q_i and Pi(Q_i^2) = Q_i^2")


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
    verify_cuntz_parity_algebra()
    verify_cuntz_susy_algebra()
