#!/usr/bin/env python3
"""SymPy witness for MobiusCantorTKKClosure.lean.

Audits the finite closure pattern:
  * Möbius atoms J:z↦1/z and Γ:z↦-z are involutive and commute projectively;
  * 4-ary Cantor boundary self-similarity via head/tail/prepend;
  * Cuntz branch orthogonality/partition on finite cylinder words;
  * TKK centralizer shadow {I,-I} squares to I and negative roots close by doubling.
"""

import itertools
import sympy as sp

z = sp.symbols("z", nonzero=True)
J = lambda w: 1 / w
G = lambda w: -w
assert sp.simplify(J(J(z)) - z) == 0
assert sp.simplify(G(G(z)) - z) == 0
assert sp.simplify(J(G(z)) - G(J(z))) == 0
assert sp.simplify(G(J(G(J(z)))) - z) == 0

# 4-ary Cantor self-similarity on finite prefixes.
def prepend(i, word):
    return (i,) + tuple(word)

def head(word):
    return word[0]

def tail(word):
    return tuple(word[1:])

word = (2, 0, 3, 1, 1)
assert prepend(head(word), tail(word)) == word
for i in range(4):
    b = (1, 2, 3)
    assert head(prepend(i, b)) == i
    assert tail(prepend(i, b)) == b

# Finite-cylinder Cuntz branch matrices: S_i prepends, T_i removes if head=i.
def words(depth, alphabet=4):
    return list(itertools.product(range(alphabet), repeat=depth))

def creation_matrix(symbol, depth):
    cod = words(depth)
    dom = words(depth - 1)
    dom_index = {w: k for k, w in enumerate(dom)}
    M = sp.zeros(len(cod), len(dom))
    for r, w in enumerate(cod):
        if w[0] == symbol:
            M[r, dom_index[w[1:]]] = 1
    return M

def annihilation_matrix(symbol, depth):
    dom = words(depth)
    cod = words(depth - 1)
    dom_index = {w: k for k, w in enumerate(dom)}
    M = sp.zeros(len(cod), len(dom))
    for r, u in enumerate(cod):
        M[r, dom_index[(symbol,) + u]] = 1
    return M

depth = 3
S = [creation_matrix(i, depth) for i in range(4)]
T = [annihilation_matrix(i, depth) for i in range(4)]
I_small = sp.eye(4 ** (depth - 1))
I_big = sp.eye(4 ** depth)
for i in range(4):
    for j in range(4):
        expected = I_small if i == j else sp.zeros(4 ** (depth - 1))
        assert T[i] * S[j] == expected
partition = sum((S[i] * T[i] for i in range(4)), sp.zeros(4 ** depth))
assert partition == I_big

# UHF cut=fractal finite average compatibility: duplicate/refine cells.
vals = [sp.symbols(f"a{i}") for i in range(4)]
refined = []
for v in vals:
    refined.extend([v, v, v, v])
assert sp.simplify(sum(refined) / len(refined) - sum(vals) / len(vals)) == 0

# TKK centralizer shadow {I,-I}.
I2 = sp.eye(2)
for C in [I2, -I2]:
    assert C * C == I2
A = sp.Matrix([[0, 1], [-1, 0]])  # A^2 = -I, so A^4 = I
assert A**2 == -I2
assert A**4 == I2

print("mobius_cantor_tkk_closure.py: all finite witnesses passed")
