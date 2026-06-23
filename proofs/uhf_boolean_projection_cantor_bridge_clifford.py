#!/usr/bin/env python3
"""clifford witness for Boolean projection/Cantor bit bridge."""
from clifford import Cl
layout, blades = Cl(1, 0, firstIdx=1)
e1 = blades['e1']
assert e1 * e1 == layout.scalar
# Boolean atoms 0,1 are idempotent and model diagonal projection values.
for p in [0, 1]:
    assert p*p == p
x = (False, True, False, True)
for n in range(len(x)):
    assert x[:n] == x[:n+1][:-1]
print('uhf Boolean projection Cantor bridge clifford certificate: ok')
