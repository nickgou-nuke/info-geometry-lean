#!/usr/bin/env python3
"""Reproducible exact CAS certificate for real Cl^+(1,3).

Signature is (+---), with e0^2=+1 and e1^2=e2^2=e3^2=-1.
The even basis is
  1, e01, e02, e03, e23, e31, e12, e0123.

The Pauli generators used here are sigma_i = e_i e_0.  They satisfy
sigma_i sigma_j = delta_ij + epsilon_ijk I sigma_k, where
I=e0123 and I^2=-1.  Thus the central Clifford pseudoscalar plays the
role of the complex unit in the Pauli/circular formulas; no analytic or
floating-point calculation is used.

This deliberately uses a tiny SymPy-backed blade implementation rather
than relying on optional clifford/galgebra APIs, so it is reproducible in a
minimal SymPy installation.  Optional package availability is reported.
"""
from __future__ import annotations

from collections import defaultdict
from fractions import Fraction
from importlib.util import find_spec
from itertools import product

import sympy as sp

# A multivector is a sparse exact SymPy-coefficient dictionary mask -> coeff.
# Bit i denotes e_i, and masks are stored in canonical increasing order.
ETA = (1, -1, -1, -1)
N = 4


def clean(d):
    return {m: sp.simplify(c) for m, c in d.items() if sp.simplify(c) != 0}


def mv(*terms):
    d = defaultdict(lambda: sp.Integer(0))
    for mask, coeff in terms:
        d[mask] += coeff
    return clean(d)


def add(a, b):
    return clean({m: a.get(m, 0) + b.get(m, 0) for m in set(a) | set(b)})


def neg(a):
    return {m: -c for m, c in a.items()}


def scale(c, a):
    return clean({m: c * v for m, v in a.items()})


def blade_product(a, b):
    """Product of canonical blades, including metric and Koszul signs."""
    common = a & b
    metric = sp.prod(ETA[i] for i in range(N) if (common >> i) & 1)
    # Number of inversions in concatenation [a-indices, b-indices].
    swaps = sum(1 for i in range(N) if (a >> i) & 1
                for j in range(N) if (b >> j) & 1 and i > j)
    return (-1) ** swaps * metric, a ^ b


def mul(a, b):
    out = defaultdict(lambda: sp.Integer(0))
    for ma, ca in a.items():
        for mb, cb in b.items():
            s, m = blade_product(ma, mb)
            out[m] += ca * cb * s
    return clean(out)


def eq(a, b):
    return clean(add(a, neg(b))) == {}


def E(i):
    return {1 << i: sp.Integer(1)}

ONE = {0: sp.Integer(1)}
e0, e1, e2, e3 = (E(i) for i in range(4))

def product_all(*xs):
    out = ONE
    for x in xs:
        out = mul(out, x)
    return out

# Canonical even basis, with e31 intentionally in geometric order 31.
e01 = mul(e0, e1)
e02 = mul(e0, e2)
e03 = mul(e0, e3)
e23 = mul(e2, e3)
e31 = mul(e3, e1)
e12 = mul(e1, e2)
I = product_all(e0, e1, e2, e3)
BASIS = [ONE, e01, e02, e03, e23, e31, e12, I]
BASIS_NAMES = ["1", "e01", "e02", "e03", "e23", "e31", "e12", "I=e0123"]

# Exact coordinate expansion in the declared basis.
def coordinates(x):
    result = []
    remainder = dict(x)
    for b in BASIS:
        # Each basis element is a signed single blade.
        assert len(b) == 1
        mask, coeff = next(iter(b.items()))
        c = remainder.pop(mask, sp.Integer(0)) / coeff
        result.append(sp.simplify(c))
    assert clean(remainder) == {}, (x, remainder)
    return tuple(result)

# 1. Full multiplication table of the eight even basis elements.
for a, b in product(BASIS, repeat=2):
    coordinates(mul(a, b))

# 2. Pseudoscalar and evenness/dimension.
assert I == {15: sp.Integer(1)}
assert mul(I, I) == {0: -1}
assert all(mask.bit_count() % 2 == 0 for x in BASIS for mask in x)
assert len({mask for x in BASIS for mask in x}) == 8
assert len(BASIS) == 8

# 3. Pauli relations. sigma_i=e_i e_0; epsilon convention epsilon_123=+1.
sigma = [mul(e1, e0), mul(e2, e0), mul(e3, e0)]
for i in range(3):
    for j in range(3):
        rhs = ONE if i == j else {}
        # epsilon term, evaluated directly for the two cyclic orientations.
        if (i, j) in ((0, 1), (1, 2), (2, 0)):
            rhs = add(rhs, mul(I, sigma[(i + 2) % 3]))
        elif (i, j) in ((1, 0), (2, 1), (0, 2)):
            rhs = add(rhs, neg(mul(I, sigma[(j + 2) % 3])))
        assert eq(mul(sigma[i], sigma[j]), rhs), (i, j)

# 4. Circular nilpotents and idempotents in the real algebra, using I as i.
s1, s2, s3 = sigma
p_plus = scale(sp.Rational(1, 2), add(ONE, s3))
p_minus = scale(sp.Rational(1, 2), add(ONE, neg(s3)))
n_plus = scale(sp.Rational(1, 2), add(s1, mul(I, s2)))
n_minus = scale(sp.Rational(1, 2), add(s1, neg(mul(I, s2))))
assert eq(mul(p_plus, p_plus), p_plus)
assert eq(mul(p_minus, p_minus), p_minus)
assert eq(mul(p_plus, p_minus), {})
assert eq(add(p_plus, p_minus), ONE)
assert eq(mul(n_plus, n_plus), {})
assert eq(mul(n_minus, n_minus), {})
assert eq(mul(n_plus, n_minus), p_plus)
assert eq(mul(n_minus, n_plus), p_minus)

print("cl13_even_cas_certificate: PASS")
print("backend: SymPy exact coefficients; optional packages:",
      ", ".join(f"{p}={'available' if find_spec(p) else 'absent'}"
                 for p in ("clifford", "galgebra")))
print("signature: (+---)")
print("even basis dimension:", len(BASIS))
print("basis:", ", ".join(BASIS_NAMES))
print("basis multiplication: PASS (64 products expanded exactly)")
print("pseudoscalar: I=e0123, I^2=-1")
print("Pauli relations: PASS, sigma_i sigma_j = delta_ij + epsilon_ijk I sigma_k")
print("circular idempotents/nilpotents: PASS")
print("n+ n-=p+, n- n+=p-, n+^2=n-^2=0")
