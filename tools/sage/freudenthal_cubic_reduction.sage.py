#!/usr/bin/env sage
"""Sage exact polynomial check for cubic-to-tripotent specialization.

Verifies in QQ[x,T1,T2,T3] that substituting T1=0, T2=-1, T3=0 in
x^3 - T1*x^2 + T2*x - T3 gives x^3 - x exactly.
"""

from sage.all import QQ, PolynomialRing

R = PolynomialRing(QQ, names=("x", "T1", "T2", "T3"))
x, T1, T2, T3 = R.gens()

cubic = x**3 - T1 * x**2 + T2 * x - T3
specialized = cubic.subs({T1: 0, T2: -1, T3: 0})
expected = x**3 - x

if specialized != expected:
    raise AssertionError(f"specialization failed: {specialized} != {expected}")

print("PASS: Sage exact Freudenthal cubic specialization")
print(f"generic={cubic}")
print(f"specialized={specialized}")
