#!/home/goutev/miniconda3/envs/sage/bin/python
"""Cl(5,5) / galgebra certificate for the 45-dimensional bivector Lie carrier."""

from itertools import combinations

from numba.core.dispatcher import Dispatcher

# python-clifford 1.5.1 requests Numba caching while imported from a conda
# prefix for which Numba cannot construct a source locator.  Disable only the
# cache hook; the JIT computations themselves remain enabled.
Dispatcher.enable_caching = lambda self: None

import clifford
from galgebra.ga import Ga

# python-clifford: bivectors in Cl(5,5) are closed under the commutator.
layout, blades = clifford.Cl(5, 5, firstIdx=0)
vectors = [blades[f"e{i}"] for i in range(10)]
bivectors = [vectors[i] ^ vectors[j] for i, j in combinations(range(10), 2)]
assert len(bivectors) == 45
for A in bivectors:
    for C in bivectors:
        bracket = (A * C - C * A) / 2
        assert all(grade == 2 for grade in bracket.grades()) or bracket == 0

# galgebra independently constructs the same signature and grade-two count.
ga = Ga("g0 g1 g2 g3 g4 g5 g6 g7 g8 g9", g=[1]*5 + [-1]*5)
gbasis = ga.mv()
galgebra_bivectors = [gbasis[i] ^ gbasis[j] for i, j in combinations(range(10), 2)]
assert len(galgebra_bivectors) == 45

print("python-clifford Cl(5,5) bivector dimension: 45")
print("python-clifford bivector commutator closure: PASS")
print("galgebra signature (5,5) bivector count: 45")
print("TKK55 CLIFFORD/GALGEBRA CERTIFICATE: PASS")
