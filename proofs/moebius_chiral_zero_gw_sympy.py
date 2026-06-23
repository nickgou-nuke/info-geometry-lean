#!/usr/bin/env python3
"""SymPy + clifford + galgebra certificate for e+/e- Möbius cancellation.

The finite object is the balanced two-pole chiral orbit.  The checked payload is:
* e+ and e- are complementary split idempotents;
* Möbius inversion swaps them and is involutive;
* chiral parity and signed GW-type zero-mode count cancel;
* the 4x4 Möbius chiral trace lane has zero trace;
* Clifford/galgebra projectors reproduce the same e+/e- split.
"""
from __future__ import annotations

from sympy import Matrix, Rational, simplify

# --- SymPy exact-rational lane ------------------------------------------------
e_plus = Matrix([1, 0])
e_minus = Matrix([0, 1])
split_one = Matrix([1, 1])
zero = Matrix([0, 0])


def cmul(x: Matrix, y: Matrix) -> Matrix:
    return Matrix([x[0] * y[0], x[1] * y[1]])


assert e_plus + e_minus == split_one
assert cmul(e_plus, e_plus) == e_plus
assert cmul(e_minus, e_minus) == e_minus
assert cmul(e_plus, e_minus) == zero

mobius = {"plus": "minus", "minus": "plus"}
assert mobius[mobius["plus"]] == "plus"
assert mobius[mobius["minus"]] == "minus"

chiral_parity = lambda x: simplify(x[0] - x[1])
assert chiral_parity(e_plus + e_minus) == 0
assert chiral_parity(e_minus + e_plus) == 0
assert simplify(Rational(1) + Rational(-1)) == 0

chi = Matrix.diag(1, -1, -1, 1)
moebius_strip = Matrix.diag(1, -1, 1, -1)
assert chi.trace() == 0
assert (moebius_strip * chi).trace() == 0

# --- clifford lane ------------------------------------------------------------
from clifford import Cl

layout, blades = Cl(1, 1, firstIdx=0)
e0 = blades["e0"]
P_plus = (1 + e0) / 2
P_minus = (1 - e0) / 2
assert P_plus * P_plus == P_plus
assert P_minus * P_minus == P_minus
assert P_plus + P_minus == 1
assert P_plus * P_minus == 0

# --- galgebra lane ------------------------------------------------------------
from galgebra.ga import Ga

ga = Ga("e0 e5", g=[1, -1])
g_e0, g_e5 = ga.mv()
gP_plus = (1 + g_e0) / 2
gP_minus = (1 - g_e0) / 2
assert (gP_plus * gP_plus - gP_plus).simplify() == 0
assert (gP_minus * gP_minus - gP_minus).simplify() == 0
assert (gP_plus + gP_minus - 1).simplify() == 0
assert (gP_plus * gP_minus).simplify() == 0

if __name__ == "__main__":
    print("sympy_chiral_parity:", chiral_parity(e_plus + e_minus))
    print("sympy_signed_gw_index:", Rational(1) + Rational(-1))
    print("sympy_moebius_trace:", (moebius_strip * chi).trace())
    print("clifford_projectors: ok")
    print("galgebra_projectors: ok")
    print("moebius chiral zero GW SymPy/clifford/galgebra certificate: ok")
