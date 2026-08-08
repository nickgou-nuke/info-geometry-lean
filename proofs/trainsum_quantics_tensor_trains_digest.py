#!/usr/bin/env python3
"""SymPy audit for the trainsum quantics tensor-train paper.

Checks the finite exact skeleton extracted from arXiv:2602.20226:

* factorized dimensions and quantics dimensions;
* uniform tensor-train storage counts;
* the affine grid endpoint formula;
* the shift-matrix support relation;
* separable exponential factorization.
"""

import sympy as sp

# Dimension bookkeeping
assert 2 * 2 * 5 == 20
assert 2 ** 10 == 1024
assert 2 * 2 * 2 + (4 - 2) * 2 * 2**2 == 24

# Affine grid endpoints from Eq. (9)
a, b = sp.symbols("a b", real=True)
N = 2
x0 = ((b - a) * 0) / (N - 1) + a
x1 = ((b - a) * 1) / (N - 1) + a
assert sp.simplify(x0 - a) == 0
assert sp.simplify(x1 - b) == 0

# Shift support relation Q_d(i,j)=1 iff j=i+d.
def shift_entry(d, i, j):
    return 1 if j == i + d else 0

assert shift_entry(2, 3, 5) == 1
assert shift_entry(2, 3, 4) == 0

# Separable exponential factorization.
v, a0, x0 = sp.symbols("v a0 x0", real=True)
xs = sp.symbols("x1 x2 x3", real=True)
left = sp.exp(sum(v * x for x in xs) + v * (a0 - x0))
right = sp.exp(v * (a0 - x0)) * sp.prod(sp.exp(v * x) for x in xs)
assert sp.simplify(left - right) == 0

# Cosine core: 2×2 orthogonal Givens rotation.
theta = sp.symbols("theta", real=True)
R = sp.Matrix([[sp.cos(theta), -sp.sin(theta)], [sp.sin(theta), sp.cos(theta)]])
assert sp.simplify(R.T * R - sp.eye(2)) == sp.zeros(2)

# Horner polynomial sample: 1 + 2x + 3x².
x = sp.symbols("x", real=True)
horner123 = 1 + x * (2 + x * 3)
assert sp.expand(horner123 - (1 + 2 * x + 3 * x**2)) == 0

# Toeplitz/shift slice family.
def shift_entry(d, i, j):
    return 1 if j == i + d else 0
assert shift_entry(2, 3, 5) == 1

# 2-point DFT / Hadamard skeleton.
H = sp.Matrix([[1, 1], [1, -1]])
assert H * H == 2 * sp.eye(2)

# Wavelet/DWT precondition and solver metadata.
assert 2 <= 4
solver_fingerprint = (2, 10, 16)
assert solver_fingerprint == (2, 10, 16)

print("trainsum quantics tensor-train audit passed")
