#!/usr/bin/env python3
"""SymPy verification of the 1+8+1 hyperbolic block model.

The block order is (plus, middle[0..7], minus), so the 10x10 metric is

    G55 = [[0,     0,       1],
           [0, eta44,       0],
           [1,     0,       0]].

This is an external symbolic derivation aid; it does not validate Lean code.
"""

import sympy as sp


n = 8
zero8 = sp.zeros(n, 1)
eta44 = sp.diag(1, 1, 1, 1, -1, -1, -1, -1)

# Endpoint-off-diagonal hyperbolic extension of eta44.
G55 = sp.zeros(n + 2)
G55[0, n + 1] = 1
G55[n + 1, 0] = 1
G55[1 : n + 1, 1 : n + 1] = eta44

x = sp.Matrix(sp.symbols("x0:8"))
y = sp.Matrix(sp.symbols("y0:8"))
a = sp.Symbol("a")

# flat(v) = eta44*v.  This matches the middle-to-endpoint signs in P and N.
flat_x = eta44 * x
flat_y = eta44 * y

P = sp.zeros(n + 2)
P[0, 1 : n + 1] = (-flat_x).T
P[1 : n + 1, n + 1] = x

N = sp.zeros(n + 2)
N[n + 1, 1 : n + 1] = (-flat_y).T
N[1 : n + 1, 0] = y

# Parameterize every eta44-skew K as K = eta44*S, where S is ordinary skew.
# This makes the hypothesis K.T*eta44 + eta44*K == 0 exact symbolically.
symbols_above_diag = {}
S = sp.zeros(n)
for i in range(n):
    for j in range(i + 1, n):
        s_ij = sp.Symbol(f"s{i}{j}")
        symbols_above_diag[i, j] = s_ij
        S[i, j] = s_ij
        S[j, i] = -s_ij
K = eta44 * S

D = sp.zeros(n + 2)
D[0, 0] = -a
D[1 : n + 1, 1 : n + 1] = K
D[n + 1, n + 1] = a


def residual(A):
    return sp.simplify(A.T * G55 + G55 * A)


def is_zero_matrix(M):
    return all(sp.simplify(entry) == 0 for entry in M)


k_hypothesis_residual = sp.simplify(K.T * eta44 + eta44 * K)
p_residual = residual(P)
n_residual = residual(N)
d_residual = residual(D)

print(f"eta44 shape: {eta44.shape}")
print(f"G55 shape: {G55.shape}")
print(f"K^T eta44 + eta44 K == 0: {is_zero_matrix(k_hypothesis_residual)}")
print(f"P^T G55 + G55 P == 0: {is_zero_matrix(p_residual)}")
print(f"N^T G55 + G55 N == 0: {is_zero_matrix(n_residual)}")
print(f"D^T G55 + G55 D == 0: {is_zero_matrix(d_residual)}")

assert is_zero_matrix(k_hypothesis_residual)
assert is_zero_matrix(p_residual)
assert is_zero_matrix(n_residual)
assert is_zero_matrix(d_residual)
print("ALL CHECKS PASSED")
