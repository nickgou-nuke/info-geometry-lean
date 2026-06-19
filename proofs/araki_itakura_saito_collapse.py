#!/usr/bin/env python3
"""
SymPy finite check for the Araki--Itakura--Saito parabolic collapse interface.

This checks the scalar information-geometric core:
  D_IS(x||y) = x/y - log(x/y) - 1
is scale invariant, is the Bregman divergence of F(x)=-log x, and matches the
Burg generator exp(K)-K-1 when x/y=exp(K).

The operator-algebraic Araki restriction is represented in Lean by an explicit
collapse premise; this script verifies the scalar target expression and the
finite parabolic nilpotent matrix model.
"""
from sympy import Matrix, exp, log, simplify, symbols, zeros

lam, x, y, K = symbols("lam x y K", nonzero=True)

D = lambda a, b: a / b - log(a / b) - 1
F = lambda z: -log(z)
gradF = lambda z: -1 / z
Bregman = lambda a, b: F(a) - F(b) - gradF(b) * (a - b)

# Common-scale invariance.
assert simplify(D(lam * x, lam * y) - D(x, y)) == 0

# Diagonal vanishing.
assert simplify(D(x, x)) == 0

# Bregman presentation for F=-log, modulo log(x/y)=log(x)-log(y) on positive cone.
bregman_expanded = simplify(Bregman(x, y).subs(log(x) - log(y), log(x / y)))
assert simplify(bregman_expanded - D(x, y)) == 0

# Burg generator form under x/y = exp(K).
burg = exp(K) - K - 1
assert simplify(D(exp(K), 1) - burg) == 0

# Finite KAN parabolic generator model.
N = Matrix([[0, 1], [0, 0]])
assert N * N == zeros(2)

if __name__ == "__main__":
    print("D_IS(x||y) =", D(x, y))
    print("D_IS(lam*x||lam*y) - D_IS(x||y) =", simplify(D(lam*x, lam*y) - D(x, y)))
    print("D_IS(x||x) =", simplify(D(x, x)))
    print("Bregman[-log](x||y) =", Bregman(x, y))
    print("D_IS(exp(K)||1) =", simplify(D(exp(K), 1)))
    print("N^2 =", N * N)
