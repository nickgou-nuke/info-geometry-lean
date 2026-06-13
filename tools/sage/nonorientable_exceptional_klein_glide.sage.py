#!/usr/bin/env sage -python
"""
Sage exact symbolic witness for the Klein-Brillouin glide model in arXiv:2504.11983v1.

Checks:
  H(kx, ky) = H(-kx, ky + pi)
  H^2 = (dx^2 + dy^2) I

This is a symbolic finite-model witness only.
"""

from sage.all import SR, matrix, identity_matrix, I, pi, sin, cos

kx, ky, alpha, beta, gamma = SR.var("kx ky alpha beta gamma")


def dx(x):
    return cos(x) + I * alpha


def dy(x, y):
    return -sin(x) * ((1 - gamma) * sin(y) + gamma * cos(y)) - SR(1) / 2 + I * beta


def H(x, y):
    dxv = dx(x)
    dyv = dy(x, y)
    return matrix(SR, [[0, dxv - I * dyv], [dxv + I * dyv, 0]])


def trig_reduce(expr):
    expr = expr.trig_simplify()
    expr = expr.subs({
        sin(-kx): -sin(kx),
        cos(-kx): cos(kx),
        sin(ky + pi): -sin(ky),
        cos(ky + pi): -cos(ky),
    })
    return expr.expand().simplify_full()


def reduce_matrix(M):
    return matrix(SR, M.nrows(), M.ncols(), [trig_reduce(M[i, j]) for i in range(M.nrows()) for j in range(M.ncols())])


def assert_zero_matrix(name, M):
    R = reduce_matrix(M)
    if any(R[i, j] != 0 for i in range(R.nrows()) for j in range(R.ncols())):
        raise AssertionError(f"{name} failed:\n{R}")
    print(f"PASS: {name}")


H0 = H(kx, ky)
Hg = H(-kx, ky + pi)
assert_zero_matrix("Klein glide symmetry H(kx,ky)=H(-kx,ky+pi)", Hg - H0)

D = dx(kx) ** 2 + dy(kx, ky) ** 2
assert_zero_matrix("two-band EP square law H^2=(dx^2+dy^2)I", H0 * H0 - D * identity_matrix(SR, 2))

print("All Sage exact Klein-glide checks passed.")
