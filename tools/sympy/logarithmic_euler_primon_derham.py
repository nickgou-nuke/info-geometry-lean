#!/usr/bin/env python3
"""
Logarithmic Euler-Primon de Rham CAS Verification.

Verifies:
1. Reflection antisymmetry of the pole logarithmic form:
   omega_poles(1 - s) = - omega_poles(s).
2. Pure imaginary velocity on the critical line:
   Re(omega_poles(1/2 + i*E)) = 0 for all E in R.
3. Primon log-differential scale decomposition:
   omega_p(s) = - ln(p) / (p^s - 1) = - ln(p) * (p^-s / (1 - p^-s)).
"""

from __future__ import annotations

import sympy as sp
from igf.cas.assertions import assert_zero


def test_logarithmic_euler_primon_derham() -> None:
    print("========================================================================")
    print("LOGARITHMIC EULER-PRIMON DE RHAM: CAS VERIFICATION")
    print("========================================================================")

    s = sp.symbols("s", complex=True)
    E = sp.symbols("E", real=True)

    # 1. Pole logarithmic differential: omega_poles(s) = 1/s + 1/(s - 1)
    omega_poles = 1 / s + 1 / (s - 1)

    # Reflection test: omega_poles(1 - s) + omega_poles(s) = 0
    omega_poles_refl = 1 / (1 - s) + 1 / ((1 - s) - 1)
    diff_refl = sp.simplify(omega_poles_refl + omega_poles)
    assert_zero(diff_refl, "omega_poles(1 - s) + omega_poles(s) = 0")
    print("  [OK] 1. Reflection Antisymmetry omega_poles(1 - s) = -omega_poles(s) verified")

    # 2. Critical Line Evaluation: s = 1/2 + i*E
    s_crit = sp.Rational(1, 2) + sp.I * E
    omega_crit = 1 / s_crit + 1 / (s_crit - 1)

    # Conjugate on critical line: conj(omega_crit) = omega(conj(s_crit)) = omega(1 - s_crit) = -omega_crit
    # Therefore 2*Re(omega_crit) = omega_crit + conj(omega_crit) = 0
    s_crit_conj = sp.Rational(1, 2) - sp.I * E
    omega_crit_conj = 1 / s_crit_conj + 1 / (s_crit_conj - 1)
    two_re = sp.simplify(omega_crit + omega_crit_conj)
    assert_zero(two_re, "Re(omega_poles(1/2 + i*E)) = 0")
    print("  [OK] 2. Critical Line Pure Imaginary Property Re(omega_poles) = 0 verified")

    # 3. Single prime mode log form geometric series equivalence
    p = sp.symbols("p", positive=True)
    omega_p = -sp.log(p) / (p**s - 1)
    omega_p_geom = -sp.log(p) * (p**(-s) / (1 - p**(-s)))
    diff_geom = sp.simplify(omega_p - omega_p_geom)
    assert_zero(diff_geom, "omega_p(s) = - ln(p) * p^-s / (1 - p^-s)")
    print("  [OK] 3. Primon Mode Bogoliubov/Geometric Series Representation verified")

    print("========================================================================")
    print("ALL LOGARITHMIC EULER-PRIMON DE RHAM INVARIANTS 100% CAS VERIFIED")
    print("========================================================================")


if __name__ == "__main__":
    test_logarithmic_euler_primon_derham()
