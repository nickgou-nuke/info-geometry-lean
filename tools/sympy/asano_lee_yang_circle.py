#!/usr/bin/env python3
"""
Asano-Lee-Yang Canonical Cayley Correspondence & Critical Line Verification.

Verifies:
1. Cayley forward/inverse cancellation:
   s(w(s)) = s,  w(s(w)) = w.
2. Canonical Riemann normalization:
   z(s) = s / (1 - s),  s(z) = z / (1 + z).
   s(z(s)) = s,  z(s(z)) = z.
3. Canonical Riemann Equivalence:
   |s / (1 - s)| = 1 <==> Re(s) = 1/2.
4. Unit circle inverse localization:
   |z| = 1, z != -1 ==> Re(z / (1 + z)) = 1/2.
5. Composed centered parameterization:
   |C(s(E) - 1/2)| = 1.
"""

from __future__ import annotations

import sympy as sp
from igf.cas.assertions import assert_zero


def test_asano_lee_yang_circle() -> None:
    print("========================================================================")
    print("ASANO LEE-YANG CANONICAL CAYLEY CORRESPONDENCE: CAS VERIFICATION")
    print("========================================================================")

    # 1. Forward/Inverse Cancellation
    s = sp.symbols("s")
    w = (1 + s) / (1 - s)
    s_rec = (w - 1) / (w + 1)
    assert_zero(sp.simplify(s_rec - s), "Cayley inverse s(w(s)) = s")
    print("  [OK] 1. Cayley Forward/Inverse Cancellation verified")

    # 2. Canonical Riemann Normalization
    z_riemann = s / (1 - s)
    s_riemann = z_riemann / (1 + z_riemann)
    assert_zero(sp.simplify(s_riemann - s), "Riemann Cayley inverse s(z(s)) = s")

    z = sp.symbols("z")
    s_of_z = z / (1 + z)
    z_of_s = s_of_z / (1 - s_of_z)
    assert_zero(sp.simplify(z_of_s - z), "Riemann Cayley forward z(s(z)) = z")
    print("  [OK] 2. Canonical Riemann Normalization Inversions verified")

    # 3. Canonical Riemann Equivalence: |s/(1-s)| = 1 <==> Re(s) = 1/2
    sigma, t = sp.symbols("sigma t", real=True)
    s_complex = sigma + sp.I * t
    norm_sq_s = sp.re(s_complex)**2 + sp.im(s_complex)**2
    norm_sq_1s = sp.re(1 - s_complex)**2 + sp.im(1 - s_complex)**2
    diff = sp.simplify(norm_sq_s - norm_sq_1s)
    # diff = sigma^2 - (1 - sigma)^2 = 2*sigma - 1
    # diff = 0 <==> sigma = 1/2
    assert_zero(sp.simplify(diff - (2 * sigma - 1)), "|s|^2 - |1-s|^2 = 2*Re(s) - 1")
    print("  [OK] 3. Canonical Equivalence |s/(1-s)|=1 <==> Re(s)=1/2 verified")

    # 4. Unit circle inverse localization: Re(z/(1+z)) = 1/2 for |z| = 1, z != -1
    theta = sp.symbols("theta", real=True)
    z_circle = sp.exp(sp.I * theta)
    s_circle = z_circle / (1 + z_circle)
    re_s_circle = sp.re(sp.simplify(s_circle))
    # exp(i theta)/(1 + exp(i theta)) = exp(i theta/2)/(2 cos(theta/2))
    # = (cos(theta/2) + i sin(theta/2))/(2 cos(theta/2)) = 1/2 + i tan(theta/2)/2
    # Re = 1/2
    re_direct = sp.simplify(sp.re((sp.cos(theta) + sp.I*sp.sin(theta)) / (1 + sp.cos(theta) + sp.I*sp.sin(theta))))
    assert_zero(sp.simplify(re_direct - sp.Rational(1, 2)), "Re(z/(1+z)) = 1/2 for |z|=1")
    print("  [OK] 4. Unit Circle Inverse Localization Re(z/(1+z)) = 1/2 verified")

    # 5. Composed Centered Parameterization
    E = sp.symbols("E", real=True)
    s_crit = sp.Rational(1, 2) + sp.I * E
    w_centered = s_crit - sp.Rational(1, 2)
    cayley_centered = (1 + w_centered) / (1 - w_centered)
    mod_sq = sp.simplify(sp.Abs(cayley_centered)**2)
    assert_zero(sp.simplify(mod_sq - 1), "|C(s(E) - 1/2)| = 1")
    print("  [OK] 5. Composed Centered Parameterization |C(s(E) - 1/2)| = 1 verified")

    print("========================================================================")
    print("ALL CANONICAL CAYLEY CORRESPONDENCE INVARIANTS 100% CAS VERIFIED")
    print("========================================================================")


if __name__ == "__main__":
    test_asano_lee_yang_circle()
