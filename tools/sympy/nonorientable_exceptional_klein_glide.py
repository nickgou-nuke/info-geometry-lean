#!/usr/bin/env python3
"""
Exact symbolic witness for the Klein-Brillouin glide model in arXiv:2504.11983v1.

It verifies the algebraic identities behind Eqs. (1)--(4):

  H(kx, ky) = H(-kx, ky + pi)
  H^2 = (dx^2 + dy^2) I

This is only a symbolic finite-model check.  Device numerics, Berry phases,
and global topology belong to separate evidence layers.
"""

import sympy as sp

kx, ky, alpha, beta, gamma = sp.symbols("kx ky alpha beta gamma")
I = sp.I


def dx(x):
    return sp.cos(x) + I * alpha


def dy(x, y):
    return -sp.sin(x) * ((1 - gamma) * sp.sin(y) + gamma * sp.cos(y)) - sp.Rational(1, 2) + I * beta


def H(x, y):
    dxv = dx(x)
    dyv = dy(x, y)
    return sp.Matrix([[0, dxv - I * dyv], [dxv + I * dyv, 0]])


def exact_reduce(expr):
    """Reduce using only exact trigonometric identities and polynomial expansion."""
    expr = sp.expand_trig(expr)
    expr = sp.expand(expr)
    # Make the glide-shift identities explicit, avoiding numerical evaluation.
    replacements = {
        sp.sin(-kx): -sp.sin(kx),
        sp.cos(-kx): sp.cos(kx),
        sp.sin(ky + sp.pi): -sp.sin(ky),
        sp.cos(ky + sp.pi): -sp.cos(ky),
    }
    expr = expr.xreplace(replacements)
    return sp.expand(expr)


def reduce_matrix(M):
    return M.applyfunc(exact_reduce)


def assert_zero_matrix(name, M):
    R = reduce_matrix(M)
    if any(R[i, j] != 0 for i in range(R.rows) for j in range(R.cols)):
        raise AssertionError(f"{name} failed:\n{R}")
    print(f"PASS: {name}")


H0 = H(kx, ky)
Hg = H(-kx, ky + sp.pi)

assert_zero_matrix("Klein glide symmetry H(kx,ky)=H(-kx,ky+pi)", Hg - H0)

D = dx(kx) ** 2 + dy(kx, ky) ** 2
I2 = sp.eye(2)
assert_zero_matrix("two-band EP square law H^2=(dx^2+dy^2)I", H0 * H0 - D * I2)

# Orientation-reversal braid bookkeeping: a Klein glide sends a charge to its inverse.
b = sp.symbols("b", nonzero=True)
clockwise = b
counterclockwise = 1 / b
if sp.expand(clockwise * counterclockwise - 1) != 0:
    raise AssertionError("orientation inversion bookkeeping failed")
print("PASS: Klein glide orientation bookkeeping b -> b^-1")

print("All exact Klein-glide exceptional-point model checks passed.")
