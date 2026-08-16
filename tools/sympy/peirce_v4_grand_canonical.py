#!/usr/bin/env python3
"""
Peirce V4 Grand Canonical Character Ensemble, Full Fourier Inversion,
Transverse Multiplier & 2D Divergence CAS Verification.

Verifies:
1. Complete 4-Component Walsh-Hadamard / Fourier Inversion:
   z0 = 1/4 (Z_pp + Z_pm + Z_mp + Z_mm)
   z1 = 1/4 (Z_pp + Z_pm - Z_mp - Z_mm)
   z2 = 1/4 (Z_pp - Z_pm + Z_mp - Z_mm)
   z3 = 1/4 (Z_pp - Z_pm - Z_mp + Z_mm)
2. 2D Flow Divergence & Redline Transverse Multiplier:
   div X(u, tau) = -2u Q - u^2 Q_u + Omega'(tau)
   div X(0, tau) = Omega'(tau)
   d/du (-u^2 Q)|_{u=0} = 0 ==> delta u(t) = delta u(0) (unit transverse multiplier)
3. Unimodular Tangential Clock (Omega' = 0):
   div X(0, tau) = 0 ==> det DPhi_t = 1 ==> -ln |det DPhi_t| = 0.
"""

from __future__ import annotations

import sympy as sp
from igf.cas.assertions import assert_zero


def test_peirce_v4_grand_canonical() -> None:
    print("========================================================================")
    print("PEIRCE V4 GRAND CANONICAL CHARACTERS & 2D FLOW: CAS VERIFICATION")
    print("========================================================================")

    z0, z1, z2, z3 = sp.symbols("z0 z1 z2 z3", real=True)

    # 1. Forward character-graded partition sums
    Z_pp = z0 + z1 + z2 + z3
    Z_pm = z0 + z1 - z2 - z3
    Z_mp = z0 - z1 + z2 - z3
    Z_mm = z0 - z1 - z2 + z3

    # Full 4-component Fourier inversion
    rec_z0 = sp.Rational(1, 4) * (Z_pp + Z_pm + Z_mp + Z_mm)
    rec_z1 = sp.Rational(1, 4) * (Z_pp + Z_pm - Z_mp - Z_mm)
    rec_z2 = sp.Rational(1, 4) * (Z_pp - Z_pm + Z_mp - Z_mm)
    rec_z3 = sp.Rational(1, 4) * (Z_pp - Z_pm - Z_mp + Z_mm)

    assert_zero(sp.simplify(rec_z0 - z0), "Fourier inversion for z0")
    assert_zero(sp.simplify(rec_z1 - z1), "Fourier inversion for z1")
    assert_zero(sp.simplify(rec_z2 - z2), "Fourier inversion for z2")
    assert_zero(sp.simplify(rec_z3 - z3), "Fourier inversion for z3")
    print("  [OK] 1. Complete 4-Component Walsh-Hadamard / Fourier Inversion verified")

    # 2. 2D Flow Divergence
    u, tau = sp.symbols("u tau", real=True)
    Q = sp.Function("Q")(u, tau)
    Omega = sp.Function("Omega")(tau)

    # X = (-u^2 Q, Omega)
    div_X = sp.diff(-u**2 * Q, u) + sp.diff(Omega, tau)
    div_redline = div_X.subs(u, 0)
    assert_zero(sp.simplify(div_redline - sp.diff(Omega, tau)), "div X(0, tau) = Omega'(tau)")
    print("  [OK] 2. Redline Divergence div X(0, tau) = Omega'(tau) verified")

    # 3. Transverse Linearized Multiplier is 0 ==> delta u(t) = delta u(0)
    transverse_jac = sp.diff(-u**2 * Q, u).subs(u, 0)
    assert_zero(sp.simplify(transverse_jac), "d/du(-u^2 Q)|_{u=0} = 0 (unit transverse linearized multiplier)")
    print("  [OK] 3. Unit Transverse Linearized Multiplier verified")

    # 4. Tangential Clock Incompressibility
    unimodular_redline = div_redline.subs(sp.diff(Omega, tau), 0)
    assert_zero(sp.simplify(unimodular_redline), "Omega' = 0 ==> div X(0, tau) = 0")
    print("  [OK] 4. Redline Unimodularity under Constant Tangential Clock verified")

    print("========================================================================")
    print("ALL PEIRCE V4 GRAND CANONICAL & 2D FLOW INVARIANTS 100% CAS VERIFIED")
    print("========================================================================")


if __name__ == "__main__":
    test_peirce_v4_grand_canonical()
