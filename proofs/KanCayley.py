#!/usr/bin/env python3
"""SymPy witness for Iwasawa (KAN) decomposition in M₂(ℂ).

This file is the computational companion to the Lean module `KanCayley.lean`.
It checks:
* compact part K(θ), scaling part A(β), unipotent shear N(z)
* determinant bookkeeping (all sectors are in det=1 sector of GL₂(ℂ))
* shear nilpotency on boundary direction: (N - I)^2 = 0
* Cayley compactification map W(s) = (s - 1/2)/(s + 1/2) and inverse
* asymptotic unification of boundary points in s -> ±∞
"""

from __future__ import annotations

import sympy as sp


I = sp.I
s, theta, beta, z = sp.symbols("s theta beta z")


I2 = sp.eye(2)


def assert_zero(name: str, expr: sp.Expr) -> None:
    simplified = sp.simplify(expr)
    assert simplified == 0, f"{name} failed: {simplified}"
    print(f"OK  {name}")


def assert_matrix_zero(name: str, mat: sp.Matrix) -> None:
    simplified = mat.applyfunc(sp.simplify)
    assert simplified == sp.zeros(*mat.shape), f"{name} failed:\n{simplified}"
    print(f"OK  {name}")


# compact rotation part (unitary phase), dilation part (scale), and nilpotent shear
K = sp.Matrix([[sp.exp(sp.I * theta), 0], [0, sp.exp(-sp.I * theta)]])
A = sp.Matrix([[sp.exp(beta), 0], [0, sp.exp(-beta)]])
N = sp.Matrix([[1, z], [0, 1]])

KAN = sp.expand(K * A * N)

assert_zero("det K = 1", sp.simplify(K.det() - 1))
assert_zero("det A = 1", sp.simplify(A.det() - 1))
assert_zero("det N = 1", sp.simplify(N.det() - 1))
assert_zero("det K*A*N = 1", sp.simplify(KAN.det() - 1))

# explicit KAN product
assert_matrix_zero(
    "KAN reconstructs upper-triangular split form",
    KAN - sp.Matrix(
        [
            [sp.exp(sp.I * theta + beta), sp.exp(sp.I * theta + beta) * z],
            [0, sp.exp(-sp.I * theta - beta)],
        ]
    ),
)

# boundary sector from shear displacement: N - I is strictly upper triangular and nilpotent
shift = N - I2
assert_matrix_zero("(N - I)^2 = 0", shift * shift)
assert_zero("det(N - I) = 0", sp.simplify(shift.det()))

# Cayley compactification around s = -1/2, with inverse map

def cayley(s: sp.Symbol | sp.Expr) -> sp.Expr:
    return (s - sp.Rational(1, 2)) / (s + sp.Rational(1, 2))


def cayley_inv(w: sp.Symbol | sp.Expr) -> sp.Expr:
    return sp.Rational(1, 2) * (1 + w) / (1 - w)

w = sp.symbols("w")
assert_zero("Cayley inverse identity", sp.simplify(cayley(cayley_inv(w)) - w))
assert_zero("inverse Cayley identity", sp.simplify(cayley_inv(cayley(s)) - s))

# boundary identification in logarithmic direction:
# in this normalization, both real infinities compactify to +1,
# while s = -1/2 is the projective pole (denominator zero).
assert_zero("Cayley real boundary at +∞ is +1", sp.simplify(sp.limit(cayley(s), s, sp.oo) - 1))
assert_zero("Cayley real boundary at -∞ is +1", sp.simplify(sp.limit(cayley(s), s, -sp.oo) - 1))

print("KanCayley.py: KAN/Cayley symbolic checks complete")
