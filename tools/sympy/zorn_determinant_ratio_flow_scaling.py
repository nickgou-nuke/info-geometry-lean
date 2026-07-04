#!/usr/bin/env python3
"""Exact SymPy verifier for Zorn determinant ratio / scalar-flow identities.

This is a computational mirror of the theorem-safe Lean sandbox:
  N(X) = a*b - u·v
  scale_r(X) = rX
  RN(X,Y) = N(Y)/N(X)
All identities are checked as polynomial identities after clearing denominators.
"""
from __future__ import annotations
import sympy as sp


def dot(u, v):
    return sum(u[i] * v[i] for i in range(3))


def norm(Z):
    a, u, v, b = Z
    return sp.expand(a * b - dot(u, v))


def scale(r, Z):
    a, u, v, b = Z
    return (r * a, [r * ui for ui in u], [r * vi for vi in v], r * b)


def components(Z):
    a, u, v, b = Z
    return [a, *u, *v, b]


def assert_poly_zero(name: str, expr):
    reduced = sp.factor(sp.expand(expr))
    if reduced != 0:
        raise AssertionError(f"{name} failed: {reduced}")
    print(f"PASS: {name}")


def assert_cell_zero(name: str, Z):
    vals = components(Z) if len(Z) == 4 and isinstance(Z[1], list) else list(Z)
    bad = [sp.factor(sp.expand(c)) for c in vals if sp.expand(c) != 0]
    if bad:
        raise AssertionError(f"{name} failed: {bad}")
    print(f"PASS: {name}")


a, b, u1, u2, u3, v1, v2, v3 = sp.symbols("a b u1 u2 u3 v1 v2 v3")
c, d, x1, x2, x3, y1, y2, y3 = sp.symbols("c d x1 x2 x3 y1 y2 y3")
r, s, t = sp.symbols("r s t")

X = (a, [u1, u2, u3], [v1, v2, v3], b)
Y = (c, [x1, x2, x3], [y1, y2, y3], d)
NX = norm(X)
NY = norm(Y)

assert_cell_zero(
    "scalar flow composes: scale_s(scale_t(X)) = scale_{s*t}(X)",
    tuple(ci - di for ci, di in zip(components(scale(s, scale(t, X))), components(scale(s*t, X))))
)

assert_poly_zero("N(scale_r(X)) = r^2 N(X)", norm(scale(r, X)) - r**2 * NX)
assert_poly_zero("N(scale_r(Y)) = r^2 N(Y)", norm(scale(r, Y)) - r**2 * NY)

# Common scaling leaves RN(X,Y)=N(Y)/N(X) invariant.  We clear denominators:
# N(rY)*N(X) - N(Y)*N(rX) = 0.
assert_poly_zero(
    "common-scaling determinant ratio invariant",
    norm(scale(r, Y)) * NX - NY * norm(scale(r, X)),
)

# Unequal scaling gives RN(scale_s X, scale_t Y) = (t/s)^2 RN(X,Y).
# Clear denominators by multiplying by s^2 * N(X) * N(scale_s X).
assert_poly_zero(
    "unequal-scaling determinant ratio factor",
    s**2 * norm(scale(t, Y)) * NX - t**2 * NY * norm(scale(s, X)),
)

# Exponential scalar flow r = exp(k tau) gives no equal-time RN drift;
# algebraically this is the derivative at a formal parameter after cancellation.
tau, k = sp.symbols("tau k")
flow_factor = sp.exp(k * tau)
ratio_residual = sp.simplify(norm(scale(flow_factor, Y)) * NX - NY * norm(scale(flow_factor, X)))
assert_poly_zero("equal-time flow derivative of ratio residual is zero", sp.diff(ratio_residual, tau))

print("ZORN_DETERMINANT_RATIO_FLOW_SCALING_OK")
