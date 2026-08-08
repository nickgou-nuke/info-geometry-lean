#!/usr/bin/env python3
"""Finite witnesses for IJIRTRiemannDigest.lean.

This is an audit script for the finite/algebraic parts of the IJIRT RH digest.
It does not prove RH, PNT, analytic continuation, or GUE universality.
"""

import sympy as sp

# CPT fixed line: s -> 1 - conjugate(s) fixes exactly Re(s)=1/2.
sigma, t = sp.symbols("sigma t", real=True)
s = sigma + sp.I * t
cpt = 1 - sp.conjugate(s)
assert sp.simplify(sp.re(cpt) - (1 - sigma)) == 0
assert sp.simplify(sp.im(cpt) - t) == 0
assert sp.solve(sp.Eq(cpt, s), sigma) == [sp.Rational(1, 2)]

# Functional equation symmetry is a pairing operation, not RH.
paired = 1 - s
assert sp.simplify(sp.re(paired) - (1 - sigma)) == 0
# Example off critical line is paired but not fixed.
off = sp.Rational(1, 3) + 7 * sp.I
assert sp.simplify(1 - sp.conjugate(off) - off) != 0

# Finite Euler-product denominator expansion.
a, b = sp.symbols("a b")
assert sp.expand((1 - a) * (1 - b)) == 1 - a - b + a * b

# Wigner-Dyson/GUE surmise elementary checks.
Delta = sp.symbols("Delta", nonnegative=True)
P = sp.pi * Delta / 2 * sp.exp(-sp.pi * Delta**2 / 4)
assert sp.simplify(P.subs(Delta, 0)) == 0
# Normalization integral over [0,∞) for the Wigner surmise.
x = sp.symbols("x", nonnegative=True)
Px = sp.pi * x / 2 * sp.exp(-sp.pi * x**2 / 4)
assert sp.simplify(sp.integrate(Px, (x, 0, sp.oo))) == 1

# Trivial zeta zeros (symbolic sanity check only).
for n in range(1, 6):
    assert sp.zeta(-2 * n) == 0

# Small finite prime-counting / average-gap audit, not asymptotic proof.
primes = list(sp.primerange(2, 100))
gaps = [q - p for p, q in zip(primes, primes[1:])]
assert len(primes) == 25
assert sum(gaps) == primes[-1] - primes[0]
assert sp.N(len(primes) / (100 / sp.log(100))) > 1  # crude finite ratio is sane order

print("ijirt_riemann_digest.py: finite witnesses passed")
