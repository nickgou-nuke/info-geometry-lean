#!/usr/bin/env python3
"""
clifford witness for the split null backbone.

This checks the corresponding Cl(4,4) lightlike generator used to interpret the
Zorn determinant's polar form as split-signature null geometry.  It proves only
finite algebraic identities in the external Python `clifford` lane.
"""

from clifford import Cl

layout, blades = Cl(4, 4, firstIdx=1)
e1 = blades["e1"]
e5 = blades["e5"]

n = e1 + e5
assert n != 0
assert n * n == 0
assert e1 * e1 == 1
assert e5 * e5 == -1

print("split_zorn_null_boundary_clifford: Cl(4,4) null generator checks passed")
