#!/usr/bin/env python3
"""
galgebra witness for the split Cl(4,4) null generator.

This mirrors the `clifford` witness with galgebra's geometric algebra engine.
No global exceptional, GNS, or Cantor-colimit theorem is claimed.
"""

from galgebra.ga import Ga

# Signature (4,4): e1^2=...=e4^2=+1, e5^2=...=e8^2=-1.
ga = Ga("e*1|2|3|4|5|6|7|8", g=[1, 1, 1, 1, -1, -1, -1, -1])
e = ga.mv()

n = e[0] + e[4]
assert str(n * n) == "0"

print("split_zorn_null_boundary_galgebra: Cl(4,4) null generator checks passed")
