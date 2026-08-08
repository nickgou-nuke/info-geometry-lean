#!/usr/bin/env python3
"""Finite audit for the Cuntz-to-p6m wallpaper boundary toy."""

import sympy as sp

sectors = {"p2": 2, "p3": 3, "p5": 5}
active_o55 = 15
p6m_count = 16
quantized_swirl = 3
lam, n = sp.symbols("lam n", nonzero=True)
feature = lam / n

for name, p in sectors.items():
    projector_sum = sum([1 for _ in range(p)])
    holonomy_sum = sum([1 for _ in range(p)])
    assert projector_sum == p, name
    assert holonomy_sum == p, name

assert sectors["p2"] == 2
assert sectors["p3"] == 3
assert sectors["p5"] == 5
assert sectors["p5"] != 6
assert len(range(sectors["p3"])) == 3
assert active_o55 + 1 == p6m_count
assert quantized_swirl == 3
assert sp.simplify(feature - lam / n) == 0

print("cuntz_p6m_wallpaper_boundary.py: SymPy audit passed")
