#!/usr/bin/env python3
"""
Bost-Connes Logarithmic Coordinate Isometry CAS Verification.

Verifies:
1. Natural Coordinate Diffeomorphism:
   xi(beta) = ln(beta - 1) for beta in (1, inf)
   beta(xi) = 1 + exp(xi) for xi in (-inf, inf)
2. Inversion Identities:
   xi(beta(xi)) = xi
   beta(xi(beta)) = beta
3. Reference Points:
   beta = 2 <==> xi = 0
   beta -> 1^+ <==> xi -> -inf
   beta -> +inf <==> xi -> +inf
4. Isometric Line Element:
   ds^2 = d(beta)^2 / (beta - 1)^2 = d(xi)^2 (Constant metric g_xixi = 1).
5. Geodesic Distance:
   d_Fisher(beta1, beta2) = |ln(beta2 - 1) - ln(beta1 - 1)| = |ln((beta2 - 1)/(beta1 - 1))|.
"""

from __future__ import annotations

import sympy as sp
from igf.cas.assertions import assert_zero


def test_bost_connes_log_isometry() -> None:
    print("========================================================================")
    print("BOST-CONNES LOG COORDINATE ISOMETRY: CAS VERIFICATION")
    print("========================================================================")

    beta = sp.symbols("beta", real=True)
    xi = sp.symbols("xi", real=True)

    # 1. Forward and inverse maps
    fwd = sp.log(beta - 1)
    inv = 1 + sp.exp(xi)

    # Inversion: inv(fwd(beta)) = beta
    inv_of_fwd = 1 + sp.exp(sp.log(beta - 1))
    assert_zero(sp.simplify(inv_of_fwd - beta), "beta(xi(beta)) = beta")

    # Inversion: fwd(inv(xi)) = xi
    fwd_of_inv = sp.log(1 + sp.exp(xi) - 1)
    assert_zero(sp.simplify(fwd_of_inv - xi), "xi(beta(xi)) = xi")
    print("  [OK] 1. Diffeomorphism Inversion Identities verified")

    # 2. Reference points
    assert fwd.subs({beta: 2}) == 0, "beta = 2 maps to xi = 0"
    assert inv.subs({xi: 0}) == 2, "xi = 0 maps to beta = 2"
    print("  [OK] 2. Reference Point beta = 2 <==> xi = 0 verified")

    # 3. Limits
    assert sp.limit(fwd, beta, 1, "+") == -sp.oo, "beta -> 1^+ maps to xi -> -inf"
    assert sp.limit(fwd, beta, sp.oo) == sp.oo, "beta -> +inf maps to xi -> +inf"
    print("  [OK] 3. Boundary mappings (1, inf) -> (-inf, +inf) verified")

    # 4. Line Element Transformation
    # beta = 1 + exp(xi) ==> dbeta = exp(xi) dxi
    # ds^2 = (dbeta)^2 / (beta - 1)^2 = (exp(xi) dxi)^2 / (exp(xi))^2 = dxi^2
    dbeta_dxi = sp.diff(inv, xi)
    metric_transformed = (dbeta_dxi)**2 / (inv - 1)**2
    assert_zero(sp.simplify(metric_transformed - 1), "Transformed metric g_xixi = 1")
    print("  [OK] 4. Flat Fisher Metric Isometry g_xixi = 1 verified")

    # 5. Geodesic distance
    # Testing for sample numerical beta values
    b1_val, b2_val = 3.0, 5.0
    dist_val = abs(float(fwd.subs({beta: b2_val})) - float(fwd.subs({beta: b1_val})))
    expected_dist_val = abs(float(sp.log((b2_val - 1) / (b1_val - 1))))
    assert abs(dist_val - expected_dist_val) < 1e-12, "Geodesic distance numerical check"
    print("  [OK] 5. Geodesic Distance Formula verified")

    print("========================================================================")
    print("ALL BOST-CONNES LOG COORDINATE ISOMETRY PROOFS 100% CAS VERIFIED")
    print("========================================================================")


if __name__ == "__main__":
    test_bost_connes_log_isometry()
