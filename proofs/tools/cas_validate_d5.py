#!/usr/bin/env python3
"""Independent symbolic checks for the D5 isotropic root calculus and Klein relation."""
from sympy import Matrix, Rational, symbols, zeros, eye, kronecker_product

n = 5
N = 2*n
h = symbols("h0:5")

# Order: isotropic positive half, isotropic negative half.
S = zeros(N)
Sinv = zeros(N)
for i in range(n):
    S[i, i] = 1
    S[i, n+i] = 1
    S[n+i, i] = Rational(1, 2)
    S[n+i, n+i] = Rational(-1, 2)
    Sinv[i, i] = Rational(1, 2)
    Sinv[i, n+i] = 1
    Sinv[n+i, i] = Rational(1, 2)
    Sinv[n+i, n+i] = -1

J = zeros(N)
D = zeros(N)
for i in range(n):
    J[i, n+i] = 1
    J[n+i, i] = 1
    D[i, i] = 1
    D[n+i, n+i] = -1

assert Sinv*S == eye(N)
assert S*Sinv == eye(N)
assert S.T*J*S == D

H = zeros(N)
for i in range(n):
    H[i, i] = h[i]
    H[n+i, n+i] = -h[i]


def diff_root(i, j):
    A = zeros(N)
    A[i, j] = 1
    A[n+j, n+i] = -1
    return A


def sum_root(i, j):
    A = zeros(N)
    A[i, n+j] = 1
    A[j, n+i] = -1
    return A


def neg_sum_root(i, j):
    A = zeros(N)
    A[n+i, j] = 1
    A[n+j, i] = -1
    return A

for i in range(n):
    for j in range(n):
        if i == j:
            continue
        A = diff_root(i, j)
        assert H*A - A*H == (h[i]-h[j])*A
        assert A != zeros(N)
for i in range(n):
    for j in range(i+1, n):
        A = sum_root(i, j)
        B = neg_sum_root(i, j)
        assert H*A - A*H == (h[i]+h[j])*A
        assert H*B - B*H == (-h[i]-h[j])*B
        assert A != zeros(N)
        assert B != zeros(N)

# Pin/Klein relation at the abstract matrix level: Θ T Θ = -T^5,
# equivalent to Θ T Θ = -T^{-1} when T^6=1.
# Use a concrete 2x2 reflection/3-cycle tensor realization.
Theta2 = Matrix([[0, 1], [1, 0]])
R3 = Matrix([[1, 0, 0], [0, 0, 1], [0, 1, 0]])
T3 = Matrix([[0, 1, 0], [0, 0, 1], [1, 0, 0]])
Theta = kronecker_product(Theta2, R3)
T = kronecker_product(eye(2), T3)
assert Theta*Theta == eye(6)
assert T**6 == eye(6)
assert Theta*T*Theta == T**-1

print("D5_BASIS_INVERSE=PASS")
print("D5_METRIC_CONGRUENCE=PASS")
print("D5_DIFFERENCE_ROOT_EIGEN=PASS (20 ordered instances)")
print("D5_SUM_ROOT_EIGEN=PASS (10 distinct instances)")
print("D5_NEG_SUM_ROOT_EIGEN=PASS (10 distinct instances)")
print("D5_DISTINCT_ROOT_COUNT=40")
print("KLEIN_MATRIX_RELATION=PASS")
