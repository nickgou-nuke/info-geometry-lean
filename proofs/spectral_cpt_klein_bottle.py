#!/usr/bin/env python3
"""SymPy witness for SpectralCPTKleinBottle.lean.

Checks the finite coordinate algebra:
  * thermal imaginary-time translation is additive;
  * CPT glide g(σ,t)=(1-σ,t) is involutive;
  * g commutes with thermal t-periodicity;
  * g fixes exactly σ=1/2;
  * g a g^{-1}=a^{-1} for scale translations, the Klein-bottle word;
  * CPT/Hill-Wheeler averaging has real part 1/2.
"""

import sympy as sp

sigma, t, T, U, a = sp.symbols("sigma t T U a", real=True)
x, y = sp.symbols("x y", real=True)


def thermal(point, period):
    s, tau = point
    return (s, tau + period)


def scale(point, shift):
    s, tau = point
    return (s + shift, tau)


def glide(point):
    s, tau = point
    return (1 - s, tau)


p = (sigma, t)

# Cylinder direction: t-translations add.
assert thermal(thermal(p, U), T) == thermal(p, U + T)

# CPT glide is an involution.
assert sp.simplify(glide(glide(p))[0] - sigma) == 0
assert sp.simplify(glide(glide(p))[1] - t) == 0

# CPT commutes with imaginary-time periodicity.
lhs = glide(thermal(p, T))
rhs = thermal(glide(p), T)
assert all(sp.simplify(l - r) == 0 for l, r in zip(lhs, rhs))

# Fixed core is sigma = 1/2.
fixed_equation = sp.Eq(1 - sigma, sigma)
assert sp.solve(fixed_equation, sigma) == [sp.Rational(1, 2)]

# Klein-bottle orientation reversal: g scale(a) g = scale(-a).
lhs = glide(scale(glide(p), a))
rhs = scale(p, -a)
assert all(sp.simplify(l - r) == 0 for l, r in zip(lhs, rhs))

# CPT/Hill-Wheeler average of s=x+iy with 1-conj(s).
avg_re = sp.simplify((x + (1 - x)) / 2)
assert avg_re == sp.Rational(1, 2)

# Mobius atoms J:z->1/z and Gamma:z->-z commute projectively.
z = sp.symbols("z", nonzero=True)
J = lambda w: 1 / w
G = lambda w: -w
assert sp.simplify(J(G(z)) - G(J(z))) == 0

print("spectral_cpt_klein_bottle.py: all finite witnesses passed")
