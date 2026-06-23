#!/usr/bin/env python3
"""Exact-rational SymPy witness for Chao retrocirculants.

Uses Chao's n=8 involutive automorphism k ↦ 5k mod 8.  Fixed indices are
0,2,4,6 and two-cycles are (1,5), (3,7).  The witness checks that the
Fourier-side normal form PσD has characteristic polynomial
Π_fixed (x-μ_k) Π_cycles (x²-μ_i μ_j).
"""

import sympy as sp


def permutation_matrix(sigma, n):
    return sp.Matrix([[1 if sigma[c] == r else 0 for c in range(n)] for r in range(n)])


def main():
    n = 8
    sigma = {k: (5 * k) % n for k in range(n)}
    assert all(sigma[sigma[k]] == k for k in range(n))
    fixed = [k for k in range(n) if sigma[k] == k]
    assert fixed == [0, 2, 4, 6]
    cycles = [(1, 5), (3, 7)]
    mu = sp.symbols('m0:8')
    x = sp.symbols('x')
    P = permutation_matrix(sigma, n)
    D = sp.diag(*mu)
    A = P * D
    char = sp.factor(A.charpoly(x).as_expr())
    expected = sp.prod(x - mu[k] for k in fixed) * sp.prod(x**2 - mu[i] * mu[j] for i, j in cycles)
    assert sp.factor(char - expected) == 0
    print("chao retrocirculant SymPy certificate: ok")


if __name__ == "__main__":
    main()
