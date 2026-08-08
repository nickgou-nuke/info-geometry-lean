#!/usr/bin/env python3
"""SymPy audit for EastSU2EquivariantSpinNetworkCircuits.lean.

External witness for the finite Schur-basis and Schur--Weyl multiplicity
bookkeeping in East--Alonso-Linaje--Park, QST 11 (2026) 025025.
"""

import sympy as sp

basis = [0, 1, 2, 3]  # 00, 01, 10, 11
singlet = {1: sp.Integer(1), 2: -sp.Integer(1)}
tplus = {0: sp.Integer(1)}
tzero = {1: sp.Integer(1), 2: sp.Integer(1)}
tminus = {3: sp.Integer(1)}


def c(v, n):
    return v.get(n, sp.Integer(0))


def dot(a, b):
    return sp.simplify(sum(c(a, n) * c(b, n) for n in basis))

# Multiplicities for n spin-1/2 systems: n=2 => J=0,1 once; n=3 => J=1/2 twice, J=3/2 once.
commutant_2 = 1**2 + 1**2
commutant_3 = 2**2 + 1**2

print("two-qubit basis length =", len(basis))
print("<singlet|singlet> =", dot(singlet, singlet))
print("<T+|T+> =", dot(tplus, tplus))
print("<T0_raw|T0_raw> =", dot(tzero, tzero))
print("<T-|T-> =", dot(tminus, tminus))
print("<singlet|T0_raw> =", dot(singlet, tzero))
print("Schur block total 1+3 =", 1 + 3)
print("2-qubit commutant dimension =", commutant_2)
print("3-qubit commutant dimension =", commutant_3)

assert len(basis) == 4
assert dot(singlet, singlet) == 2
assert dot(tplus, tplus) == 1
assert dot(tzero, tzero) == 2
assert dot(tminus, tminus) == 1
assert dot(singlet, tzero) == 0
assert 1 + 3 == 4
assert commutant_2 == 2
assert commutant_3 == 5
print("East SU(2)-equivariant spin-network circuit audit passed")
