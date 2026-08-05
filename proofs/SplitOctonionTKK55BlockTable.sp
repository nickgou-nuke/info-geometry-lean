#!/usr/bin/env python3
"""SymPy sanity witness for the 1+4+1 TKK block table.

This is an independent symbolic check only; Lean remains the authority.
"""

import sympy as sp


def skew_symbols(prefix):
    out = sp.zeros(4)
    for i in range(4):
        for j in range(i + 1, 4):
            q = sp.symbols(f"{prefix}{i}{j}")
            out[i, j] = q
            out[j, i] = -q
    return out


H = sp.diag(1, 1, -1, -1)
S = skew_symbols("s")
U = skew_symbols("u")
K = H * S
L = H * U

x = sp.Matrix(sp.symbols("x0:4"))
y = sp.Matrix(sp.symbols("y0:4"))
z = sp.Matrix(sp.symbols("z0:4"))
a, b = sp.symbols("a b")


def beta(u, v):
    return (u.T * H * v)[0]


def rank_two(u, v):
    return v * (u.T * H) - u * (v.T * H)


def block(a11, a12, a13, a21, a22, a23, a31, a32, a33):
    return sp.Matrix.vstack(
        sp.Matrix.hstack(a11, a12, a13),
        sp.Matrix.hstack(a21, a22, a23),
        sp.Matrix.hstack(a31, a32, a33),
    )


zero14 = sp.zeros(1, 4)
zero41 = sp.zeros(4, 1)
zero44 = sp.zeros(4)


def P(u):
    return block(sp.zeros(1), zero14, sp.zeros(1), u, zero44,
                 zero41, sp.zeros(1), -(u.T * H), sp.zeros(1))


def N(v):
    return block(sp.zeros(1), -(v.T * H), sp.zeros(1), zero41,
                 zero44, v, sp.zeros(1), zero14, sp.zeros(1))


def D(scalar, matrix):
    return block(sp.Matrix([[scalar]]), zero14, sp.zeros(1), zero41,
                 matrix, zero41, sp.zeros(1), zero14, sp.Matrix([[-scalar]]))


def assert_zero(matrix, name):
    residual = matrix.applyfunc(sp.expand)
    assert all(entry == 0 for entry in residual), f"failed: {name}\n{residual}"


assert_zero(K.T * H + H * K, "K is H-skew")
assert_zero(L.T * H + H * L, "L is H-skew")
assert_zero(D(a, K) * P(x) - P(K * x - a * x) - P(x) * D(a, K), "[D,P]")
assert_zero(D(a, K) * N(y) - N(K * y + a * y) - N(y) * D(a, K), "[D,N]")
assert_zero(D(a, K) * D(b, L) - D(b, L) * D(a, K)
            - D(0, K * L - L * K), "[D,D]")
assert_zero(P(x) * P(y) - P(y) * P(x), "[P,P]")
assert_zero(N(x) * N(y) - N(y) * N(x), "[N,N]")
assert_zero(P(x) * N(y) - N(y) * P(x) - D(beta(x, y), rank_two(x, y)), "[P,N]")

triple = beta(x, y) * z + beta(z, y) * x - beta(x, z) * y
assert_zero((N(y) * P(x) - P(x) * N(y)) * P(z)
            - P(z) * (N(y) * P(x) - P(x) * N(y)) - P(triple),
            "spin-factor triple")

print("SYMPY_TKK55_BLOCK_TABLE=PASS")
