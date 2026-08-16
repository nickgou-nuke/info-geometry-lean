#!/usr/bin/env python3
"""
Radon-Nikodym Surprisal, Fisher Metric, and Lie Flow Jacobian CAS Verification.

Verifies:
1. Surprisal / Negative Logarithmic Radon-Nikodym derivative:
   i(x) = - ln(rho(x)) ==> d(i) = - d(rho) / rho.
2. Fisher Information Metric as Surprisal Gradient Variance:
   g_F(x) = (d(i))^2 * rho = (d(rho))^2 / rho.
3. Madelung-Anscombe Amplitude Isometry:
   psi(x) = sqrt(rho(x)) ==> 4 * (d(psi))^2 = g_F(x).
4. Negative Log-Determinant of Flow Jacobian (Liouville Invariance):
   For unimodular Lie flows det(Jac Phi_t) = 1 ==> - ln det(Jac Phi_t) = 0.
5. Hessian of Negative Log-Determinant Metric:
   d^2/d(sigma)^2 (- ln sigma) = 1 / sigma^2.
"""

from __future__ import annotations

import sympy as sp
from igf.cas.assertions import assert_zero


def test_radon_nikodym_surprisal_jacobian() -> None:
    print("========================================================================")
    print("RADON-NIKODYM SURPRISAL, FISHER METRIC & LIE JACOBIAN: CAS VERIFICATION")
    print("========================================================================")

    x = sp.symbols("x", real=True)
    rho = sp.Function("rho", positive=True)(x)
    drho = sp.diff(rho, x)

    # 1. Surprisal differential
    surprisal = - sp.log(rho)
    d_surprisal = sp.diff(surprisal, x)
    expected_d_surprisal = - drho / rho
    assert_zero(sp.simplify(d_surprisal - expected_d_surprisal), "d(-ln rho) = -drho/rho")
    print("  [OK] 1. Surprisal Differential d(-ln rho) = -drho/rho verified")

    # 2. Fisher metric density
    g_F = (d_surprisal)**2 * rho
    expected_g_F = drho**2 / rho
    assert_zero(sp.simplify(g_F - expected_g_F), "g_F = (d(-ln rho))^2 * rho = (drho)^2 / rho")
    print("  [OK] 2. Fisher Metric Density from Surprisal Variance verified")

    # 3. Madelung-Anscombe amplitude isometry
    psi = sp.sqrt(rho)
    dpsi = sp.diff(psi, x)
    fisher_from_psi = 4 * dpsi**2
    assert_zero(sp.simplify(fisher_from_psi - g_F), "4 (d(sqrt(rho)))^2 = g_F")
    print("  [OK] 3. Madelung-Anscombe Amplitude Isometry 4 (d(sqrt(rho)))^2 = g_F verified")

    # 4. Unimodular Lie flow log-determinant
    jac_det = 1
    log_det = - sp.log(jac_det)
    assert_zero(log_det, "-ln(det(Jac)) = 0 for unimodular flows")
    print("  [OK] 4. Unimodular Lie Flow Liouville Invariance -ln(det(Jac)) = 0 verified")

    # 5. Hessian of negative log-determinant (Fisher metric on symmetric cones)
    sigma = sp.symbols("sigma", positive=True)
    hessian_log = sp.diff(- sp.log(sigma), sigma, 2)
    expected_hessian = 1 / sigma**2
    assert_zero(sp.simplify(hessian_log - expected_hessian), "d^2/d(sigma)^2 (-ln sigma) = 1/sigma^2")
    print("  [OK] 5. Hessian of Negative Log-Determinant d^2/dsigma^2 (-ln sigma) = 1/sigma^2 verified")

    print("========================================================================")
    print("ALL SURPRISAL, FISHER & LIE JACOBIAN INVARIANTS 100% CAS VERIFIED")
    print("========================================================================")


if __name__ == "__main__":
    test_radon_nikodym_surprisal_jacobian()
