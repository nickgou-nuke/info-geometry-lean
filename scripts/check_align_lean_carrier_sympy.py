#!/usr/bin/env python3
"""Independent symbolic GF(2) check of the first aligned carrier identity."""
import sympy as sp

def M(rows):
    return sp.Matrix([[int(j in row) for j in range(1, 9)] for row in rows])

gens = [
    M([[1,4],[2,4],[3,8],[4],[4,5,6],[6],[1,2,4,7,8],[8]]),
    M([[1,8],[2,8],[3],[3,4],[1,2,4,5,8],[3,4,6,7,8],[3,7,8],[8]]),
    M([[1,3,8],[2,3,8],[3],[4,8],[1,2,4,5,7],[1,2,3,4,6,8],[3,7,8],[8]]),
    M([[1],[2],[3],[4],[4,5],[6],[7,8],[8]]),
    M([[1,8],[2,8],[3],[4],[1,2,4,5,8],[4,6],[3,7,8],[8]]),
    M([[1],[2],[3],[4],[3,5],[6,8],[7],[8]]),
]
s = M([[1],[2],[4],[3],[5],[7],[6],[8]])
lhs = (s.inv() * gens[0] * s).applyfunc(lambda x: x % 2)
rhs = (gens[2] * gens[4]).applyfunc(lambda x: x % 2)
assert lhs == rhs
assert all((g * g).applyfunc(lambda x: x % 2) == sp.eye(8) for g in gens[:1] + gens[3:])
print("SYMPY_LEAN_S_CONJ_PC1=PASS")
print("SYMPY_LEAN_S_CONJ_PC1_WORD=[0,0,1,0,1,0]")
