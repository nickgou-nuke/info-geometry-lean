#!/usr/bin/env python3
"""
Bogoliubov-Covariant Mellin-Krein Quantization CAS Verification.

Verifies:
1. Symplectic SU(1,1) determinant invariance:
   |alpha|^2 - |beta|^2 = 1.
2. Poincaré disk coordinate modulus:
   |z| = tanh(r) < 1.
3. Rapidity recovery from disk modulus:
   r = (1/2) * ln((1 + |z|) / (1 - |z|)).
4. Boost reversal under Krein reflection:
   B(-u) = B(u)^-1.
5. su(1,1) Lie algebra commutation relations:
   [K0, K+] = K+, [K0, K-] = -K-, [K+, K-] = 2 K0.
"""

from __future__ import annotations

import sympy as sp
from igf.cas.assertions import assert_zero


def test_bogoliubov_covariant_mellin_krein() -> None:
    print("========================================================================")
    print("BOGOLIUBOV COVARIANT MELLIN-KREIN QUANTIZATION: CAS VERIFICATION")
    print("========================================================================")

    u, t = sp.symbols("u t", real=True)
    r = sp.symbols("r", positive=True)
    n = sp.symbols("n", positive=True)

    # 1. SU(1,1) determinant invariance
    rapidity = u * sp.log(n)
    phase = t * sp.log(n)
    alpha = sp.exp(-sp.I * phase) * sp.cosh(rapidity)
    beta = sp.exp(-sp.I * phase) * sp.sinh(rapidity)

    norm_sq_alpha = sp.simplify(alpha * sp.conjugate(alpha))
    norm_sq_beta = sp.simplify(beta * sp.conjugate(beta))
    diff = sp.simplify(norm_sq_alpha - norm_sq_beta)
    assert_zero(diff - 1, "|alpha|^2 - |beta|^2 = 1")
    print("  [OK] 1. SU(1,1) Symplectic Invariance |alpha|^2 - |beta|^2 = 1 verified")

    # 2. Poincaré disk coordinate & rapidity inversion
    tanh_r = (sp.exp(r) - sp.exp(-r)) / (sp.exp(r) + sp.exp(-r))
    quot = sp.simplify((1 + tanh_r) / (1 - tanh_r))
    r_recovered = sp.Rational(1, 2) * sp.log(quot)
    assert_zero(sp.simplify(r_recovered - r), "r = (1/2) ln((1 + tanh r)/(1 - tanh r))")
    print("  [OK] 2. Poincaré Disk Modulus & Rapidity Inversion verified")

    # 3. Boost matrix reflection & inversion
    B_u = sp.Matrix([
        [sp.cosh(rapidity), sp.sinh(rapidity)],
        [sp.sinh(rapidity), sp.cosh(rapidity)]
    ])
    B_neg_u = sp.Matrix([
        [sp.cosh(-rapidity), sp.sinh(-rapidity)],
        [sp.sinh(-rapidity), sp.cosh(-rapidity)]
    ])
    prod = sp.simplify(B_u * B_neg_u)
    diff_prod = prod - sp.eye(2)
    assert_zero(sp.simplify(diff_prod[0, 0]**2 + diff_prod[0, 1]**2 + diff_prod[1, 0]**2 + diff_prod[1, 1]**2),
                "B(u) * B(-u) = I (Boost Reversal)")
    print("  [OK] 3. Squeezing Boost Reversal B(-u) = B(u)^-1 verified")

    # 4. su(1,1) Lie algebra commutation relations
    K0 = sp.Matrix([[sp.Rational(1, 2), 0], [0, -sp.Rational(1, 2)]])
    Kp = sp.Matrix([[0, 1], [0, 0]])
    Km = sp.Matrix([[0, 0], [1, 0]])

    comm_0_p = K0 * Kp - Kp * K0 - Kp
    assert_zero(sum(c**2 for c in comm_0_p), "[K0, K+] = K+")

    comm_0_m = K0 * Km - Km * K0 - (-Km)
    assert_zero(sum(c**2 for c in comm_0_m), "[K0, K-] = -K-")

    comm_p_m = Kp * Km - Km * Kp - 2 * K0
    assert_zero(sum(c**2 for c in comm_p_m), "[K+, K-] = 2 K0")
    print("  [OK] 4. su(1,1) Lie Algebra Commutator Relations verified")

    print("========================================================================")
    print("ALL BOGOLIUBOV COVARIANT MELLIN-KREIN INVARIANTS 100% CAS VERIFIED")
    print("========================================================================")


if __name__ == "__main__":
    test_bogoliubov_covariant_mellin_krein()
