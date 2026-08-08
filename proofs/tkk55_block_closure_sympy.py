#!/usr/bin/env python3
"""Exact symbolic certificate for the 1+8+1 TKK/so(5,5) block model.

The block order agrees with SplitOctonionTKK55Blocks:
    (minus, middle[0..7], plus).
This is a derivation aid, not a substitute for Lean kernel checking.
"""

import sympy as sp

n = 8
B = sp.diag(1, 1, 1, 1, -1, -1, -1, -1)
G = sp.zeros(10)
G[0, 9] = G[9, 0] = 1
G[1:9, 1:9] = B


def flat(v):
    return (v.T * B)


def P(x):
    A = sp.zeros(10)
    A[1:9, 0] = x
    A[9, 1:9] = -flat(x)
    return A


def N(y):
    A = sp.zeros(10)
    A[0, 1:9] = -flat(y)
    A[1:9, 9] = y
    return A


def D(a, K):
    A = sp.zeros(10)
    A[0, 0] = a
    A[1:9, 1:9] = K
    A[9, 9] = -a
    return A


def comm(A, C):
    return sp.expand(A * C - C * A)


def zero(M):
    return all(sp.expand(z) == 0 for z in M)


x = sp.Matrix(sp.symbols("x0:8"))
y = sp.Matrix(sp.symbols("y0:8"))
z = sp.Matrix(sp.symbols("z0:8"))
a, b = sp.symbols("a b")

# Every B-skew matrix is B*S for an ordinary skew matrix S.
S = sp.zeros(8)
T = sp.zeros(8)
for i in range(8):
    for j in range(i + 1, 8):
        sij = sp.Symbol(f"s{i}_{j}")
        tij = sp.Symbol(f"t{i}_{j}")
        S[i, j], S[j, i] = sij, -sij
        T[i, j], T[j, i] = tij, -tij
K, L = B * S, B * T

beta_xy = (x.T * B * y)[0]
Kxy = y * flat(x) - x * flat(y)

checks = {
    "metric symmetric": G.T == G,
    "metric involutive": zero(G * G - sp.eye(10)),
    "K is B-skew": zero(K.T * B + B * K),
    "P orthogonal": zero(P(x).T * G + G * P(x)),
    "N orthogonal": zero(N(y).T * G + G * N(y)),
    "D orthogonal": zero(D(a, K).T * G + G * D(a, K)),
    "[P,P]=0": zero(comm(P(x), P(y))),
    "[N,N]=0": zero(comm(N(x), N(y))),
    "[P,N] formula": zero(comm(P(x), N(y)) - D(beta_xy, Kxy)),
    "[D,P] formula": zero(comm(D(a, K), P(x)) - P(K * x - a * x)),
    "[D,N] formula": zero(comm(D(a, K), N(y)) - N(K * y + a * y)),
    "[D,D] formula": zero(comm(D(a, K), D(b, L)) - D(0, comm(K, L))),
}

# Converse: solve A^T G + G A = 0 entrywise and verify unique reconstruction.
q = sp.symbols("q0:100")
A = sp.Matrix(10, 10, q)
R = A.T * G + G * A
constraints = [sp.expand(R[i, j]) for i in range(10) for j in range(i, 10)]
coefficient_matrix, _ = sp.linear_eq_to_matrix(constraints, q)
constraint_rank = coefficient_matrix.rank()
solution_dimension = 100 - constraint_rank

# Structural basis: 8 P, 1 dilation, 28 B-skew middle, 8 N.
columns = []
for i in range(8):
    e = sp.eye(8)[:, i]
    columns.append(sp.Matrix(P(e)).reshape(100, 1))
columns.append(sp.Matrix(D(1, sp.zeros(8))).reshape(100, 1))
for i in range(8):
    for j in range(i + 1, 8):
        E = sp.zeros(8)
        E[i, j], E[j, i] = 1, -1
        columns.append(sp.Matrix(D(0, B * E)).reshape(100, 1))
for i in range(8):
    e = sp.eye(8)[:, i]
    columns.append(sp.Matrix(N(e)).reshape(100, 1))
block_basis_rank = sp.Matrix.hstack(*columns).rank()

# Jordan spin-factor triple using the convention [[N(y),P(x)],P(z)].
spin_triple = beta_xy * z + (z.T * B * y)[0] * x - (x.T * B * z)[0] * y
checks["spin triple"] = zero(comm(comm(N(y), P(x)), P(z)) - P(spin_triple))

for name, ok in checks.items():
    print(f"{name}: {ok}")
    assert ok, name
print(f"orthogonality constraint rank: {constraint_rank}")
print(f"orthogonal solution dimension: {solution_dimension}")
print(f"P+D+N block basis rank: {block_basis_rank}")
assert constraint_rank == 55
assert solution_dimension == 45
assert block_basis_rank == 45
print("TKK55 BLOCK CLOSURE: PASS")
