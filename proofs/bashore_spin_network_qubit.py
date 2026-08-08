#!/usr/bin/env python3
"""SymPy audit for BashoreSpinNetworkQubit.lean.

External witness for the four-valent j=1/2 intertwiner-qubit coefficients in
Erik Bashore's LQG spin-network quantum simulation report.
"""

import sympy as sp

support = [3, 5, 6, 9, 10, 12]  # 0011,0101,0110,1001,1010,1100

c0 = {5: sp.Rational(1, 2), 6: -sp.Rational(1, 2), 9: -sp.Rational(1, 2), 10: sp.Rational(1, 2)}
c1raw = {
    3: sp.Integer(1),
    12: sp.Integer(1),
    5: -sp.Rational(1, 2),
    6: -sp.Rational(1, 2),
    9: -sp.Rational(1, 2),
    10: -sp.Rational(1, 2),
}


def coeff(table, n):
    return table.get(n, sp.Integer(0))


def dot(a, b):
    return sp.simplify(sum(coeff(a, n) * coeff(b, n) for n in support))

norm0 = dot(c0, c0)
norm1raw = dot(c1raw, c1raw)
orth = dot(c0, c1raw)

print("physical qubit basis card =", 16)
print("intertwiner qubit dimension =", 2)
print("support length =", len(support))
print("<0I|0I> =", norm0)
print("<1I_raw|1I_raw> =", norm1raw)
print("<0I|1I_raw> =", orth)
print("normalized |1I> scale = 1/sqrt(3)")

assert len(support) == 6
assert norm0 == 1
assert norm1raw == 3
assert orth == 0
print("Bashore spin-network qubit audit passed")
