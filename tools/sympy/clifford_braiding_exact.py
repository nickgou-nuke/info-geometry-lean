#!/usr/bin/env python3
"""
Exact Clifford braid verifier over Cl(n,0) using a small symbolic Clifford engine.

Checks B_i=(1+e_i e_{i+1})/sqrt(2):
  B_i^2 = e_i e_{i+1}, B_i^4=-1, B_i^8=1,
  B_i B_{i+1} B_i = B_{i+1} B_i B_{i+1},
  B_i B_j = B_j B_i for |i-j|>1.
"""

from __future__ import annotations
from collections import defaultdict
import sympy as sp

sqrt2 = sp.sqrt(2)


def blade_mul(mask_a: int, mask_b: int):
    """Euclidean Clifford product of basis blades encoded by bit masks."""
    sign = 1
    x = mask_a
    i = 0
    while x:
        if x & 1:
            inversions = (mask_b & ((1 << i) - 1)).bit_count()
            if inversions % 2:
                sign = -sign
        x >>= 1
        i += 1
    return sign, mask_a ^ mask_b


class Cl:
    def __init__(self, terms=None):
        self.terms = {}
        if terms:
            for k, v in terms.items():
                vv = sp.simplify(v)
                if vv != 0:
                    self.terms[int(k)] = vv

    def __add__(self, other):
        out = defaultdict(lambda: 0)
        for k, v in self.terms.items():
            out[k] += v
        for k, v in other.terms.items():
            out[k] += v
        return Cl(out)

    def __neg__(self):
        return Cl({k: -v for k, v in self.terms.items()})

    def __sub__(self, other):
        return self + (-other)

    def __mul__(self, other):
        if not isinstance(other, Cl):
            return Cl({k: sp.simplify(v * other) for k, v in self.terms.items()})
        out = defaultdict(lambda: 0)
        for a, ca in self.terms.items():
            for b, cb in other.terms.items():
                s, m = blade_mul(a, b)
                out[m] += s * ca * cb
        return Cl(out)

    def __rmul__(self, other):
        return Cl({k: sp.simplify(other * v) for k, v in self.terms.items()})

    def simplify(self):
        return Cl({k: sp.simplify(v) for k, v in self.terms.items()})

    def is_zero(self):
        return all(sp.simplify(v) == 0 for v in self.terms.values())

    def __repr__(self):
        return repr(self.simplify().terms)


def scalar(c):
    return Cl({0: c})


def e(i):
    return Cl({1 << i: 1})


def cpow(x, n):
    out = scalar(1)
    for _ in range(n):
        out = (out * x).simplify()
    return out


def assert_zero(name, x):
    y = x.simplify()
    if not y.is_zero():
        raise AssertionError(f"{name} failed: {y}")
    print(f"PASS: {name}")


I = scalar(1)


def B(i):
    return (I + e(i) * e(i + 1)) * (1 / sqrt2)


for i in range(3):
    assert_zero(f"B_{i}^2 = e_{i}e_{i+1}", B(i) * B(i) - e(i) * e(i + 1))
    assert_zero(f"B_{i}^4 = -1", cpow(B(i), 4) + I)
    assert_zero(f"B_{i}^8 = 1", cpow(B(i), 8) - I)

assert_zero("adjacent Artin relation B0 B1 B0 = B1 B0 B1",
            B(0) * B(1) * B(0) - B(1) * B(0) * B(1))
assert_zero("far commutation B0 B2 = B2 B0",
            B(0) * B(2) - B(2) * B(0))

print("All exact Clifford braiding checks passed.")
