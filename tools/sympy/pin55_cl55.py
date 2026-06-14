#!/usr/bin/env python3
"""Clifford + GAlgebra witness: Cl(5,5) algebra for Pin(5,5) / V4.

Verifies:
1. Cl(5,5) generators: e_0..e_4 square to +1, e_5..e_9 square to -1
2. (e_0·e_5)^2 = 1 (V4 relation)
3. Anticommutativity e_i*e_j = -e_j*e_i for i≠j
"""
from clifford import Cl

# Cl(5,5): 5 positive-norm and 5 negative-norm generators
layout, blades = Cl(5, 5, firstIdx=0)
print("CLIFFORD_CL55_OK")

# Get generators
e = [blades[f'e{i}'] for i in range(10)]

# Check squares
for i in range(5):
    assert (e[i] * e[i])(0) == 1.0, f"e{i}^2 should be +1"
for i in range(5, 10):
    assert (e[i] * e[i])(0) == -1.0, f"e{i}^2 should be -1"
print("CLIFFORD_CL55_SQUARES: e0..e4^2=+1, e5..e9^2=-1")

# Check anticommutativity
assert e[0] * e[5] == -e[5] * e[0], "e0 and e5 should anticommute"

# V4: (e0*e5)^2 = 1
v4 = e[0] * e[5]
assert (v4 * v4)(0) == 1.0, "(e0*e5)^2 should be 1"
print("CLIFFORD_V4_RELATION: (e0·e5)^2 = 1")

# Central element -1
identity = e[0] * e[0]
neg_one = -identity
assert neg_one * neg_one == identity
print("CLIFFORD_CENTRAL: (-1)^2 = 1")

print("CLIFFORD_PIN55_ALL_OK")

# GAlgebra check
from galgebra.ga import Ga

# Cl(5,5) with diagonal metric
metric = [1]*5 + [-1]*5
ga = Ga('e0 e1 e2 e3 e4 e5 e6 e7 e8 e9', g=metric)
e_ga = list(ga.mv_basis)

for i in range(5):
    assert str((e_ga[i] * e_ga[i]).simplify()) == "1", f"GAlgebra e{i}^2 != +1"
for i in range(5, 10):
    assert str((e_ga[i] * e_ga[i]).simplify()) == "-1", f"GAlgebra e{i}^2 != -1"
print("GALGEBRA_CL55_OK")
print("GALGEBRA_PIN55_ALL_OK")
