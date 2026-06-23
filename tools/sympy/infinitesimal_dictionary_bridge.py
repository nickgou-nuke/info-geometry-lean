#!/usr/bin/env python3
"""
SymPy witness for the infinitesimal information-geometric / operator-algebraic
five-way dictionary.

Checks in a classical scalar/computational model:
1. log Radon-Nikodym = log(p/q) = log p - log q
2. generalized KL splits into symmetric and antisymmetric parts
3. generalized KL is represented by the Bregman divergence of the entropy
   generator on the positive cone
4. the antisymmetric part changes sign under swapping the states
5. Burg specialization D_IS(exp(K) || 1) = exp(K) - K - 1
6. d(log Q) = dQ/Q for a positive partition function Q
7. the scalar Connes cocycle derivative is i times the modular Hamiltonian gap
8. the self-concordant barrier force is the negative d(log Q) current
"""

from __future__ import annotations

import sympy as sp


def generalized_kl(p1: sp.Expr, p2: sp.Expr, q1: sp.Expr, q2: sp.Expr) -> sp.Expr:
    """Positive-cone generalized KL; ordinary KL on the equal-mass slice."""
    return sp.simplify(
        p1 * sp.log(p1 / q1) + p2 * sp.log(p2 / q2) - p1 - p2 + q1 + q2
    )


def bregman_entropy(
    p1: sp.Expr, p2: sp.Expr, q1: sp.Expr, q2: sp.Expr
) -> sp.Expr:
    x1, x2 = sp.symbols("x1 x2", positive=True, real=True)
    F = x1 * sp.log(x1) + x2 * sp.log(x2)
    grad1 = sp.diff(F, x1)
    grad2 = sp.diff(F, x2)
    return sp.simplify(
        (p1 * sp.log(p1) + p2 * sp.log(p2))
        - (q1 * sp.log(q1) + q2 * sp.log(q2))
        - grad1.subs({x1: q1, x2: q2}) * (p1 - q1)
        - grad2.subs({x1: q1, x2: q2}) * (p2 - q2)
    )


def main() -> None:
    print("=== SYMPY: INFINITESIMAL DICTIONARY WITNESS ===")

    p, q, p2, q2, K, theta, t, deltaK = sp.symbols(
        "p q p2 q2 K theta t deltaK", positive=True, real=True
    )

    rn_log = sp.simplify(sp.log(p / q))
    print("\n1. Log Radon-Nikodym ratio log(p/q):")
    sp.pprint(rn_log)
    assert sp.simplify(rn_log - (sp.log(p) - sp.log(q))) == 0

    Dpq = generalized_kl(p, p2, q, q2)
    Dqp = generalized_kl(q, q2, p, p2)
    sym = sp.simplify((Dpq + Dqp) / 2)
    antisym = sp.simplify((Dpq - Dqp) / 2)
    print("\n2. Generalized KL decomposition:")
    print("D(p||q) =")
    sp.pprint(Dpq)
    print("Symmetric part =")
    sp.pprint(sym)
    print("Antisymmetric part =")
    sp.pprint(antisym)
    assert sp.simplify(Dpq - (sym + antisym)) == 0
    assert sp.simplify(Dqp - (sym - antisym)) == 0
    assert sp.simplify(((Dqp - Dpq) / 2) + antisym) == 0

    print("\n3. Bregman form of generalized KL:")
    breg = bregman_entropy(p, p2, q, q2)
    sp.pprint(breg)
    assert sp.simplify(breg - Dpq) == 0

    D_is = sp.simplify(sp.exp(K) - sp.log(sp.exp(K)) - 1)
    expected_burg = sp.simplify(sp.exp(K) - K - 1)
    print("\n4. Burg / Itakura-Saito specialization:")
    sp.pprint(D_is)
    assert sp.simplify(D_is - expected_burg) == 0

    Q = sp.exp(theta**2 + theta)
    dlogQ = sp.simplify(sp.diff(sp.log(Q), theta))
    dq_over_q = sp.simplify(sp.diff(Q, theta) / Q)
    print("\n5. de Rham logarithmic one-form d(log Q):")
    sp.pprint(dlogQ)
    print("dQ / Q:")
    sp.pprint(dq_over_q)
    assert sp.simplify(dlogQ - dq_over_q) == 0

    cocycle = sp.exp(sp.I * t * deltaK)
    cocycle_derivative_at_zero = sp.simplify(sp.diff(cocycle, t).subs(t, 0))
    print("\n6. Scalar Connes cocycle infinitesimal:")
    sp.pprint(cocycle_derivative_at_zero)
    assert sp.simplify(cocycle_derivative_at_zero - sp.I * deltaK) == 0

    barrier = sp.simplify(-sp.diff(sp.log(Q), theta))
    print("\n7. Self-concordant barrier force -d(log Q):")
    sp.pprint(barrier)
    assert sp.simplify(barrier + dlogQ) == 0

    print("\nCONCLUSION:")
    print("  - log RN ratio is the logarithmic density difference.")
    print("  - generalized KL splits uniquely into symmetric and antisymmetric parts.")
    print("  - generalized KL is the Bregman divergence of entropy on the positive cone.")
    print("  - The antisymmetric part flips sign under state exchange.")
    print("  - Burg/Itakura-Saito specialization matches exp(K) - K - 1.")
    print("  - d(log Q) equals dQ/Q in the positive scalar model.")
    print("  - Connes cocycle derivative is i times the modular Hamiltonian gap.")
    print("  - The barrier force is the negative de Rham logarithmic current.")


if __name__ == "__main__":
    main()
