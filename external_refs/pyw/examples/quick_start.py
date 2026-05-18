#!/usr/bin/env python3
"""
Quick Start Example for pyw Library

This example demonstrates the basic usage of pyw for working with
fractional levels and admissible weights in affine Kac-Moody algebras.
"""

import sys

sys.path.insert(0, "/Users/lelouch/pyw")

from fractions import Fraction

# Import pyw classes
from pyw.fractional.level import FractionalLevel
from pyw.fractional.admissible import AdmissibleWeight
from pyw.core.weight_space import FractionalWeightSpace

print("=" * 70)
print("pyw Quick Start Example")
print("=" * 70)

# Example 1: Create a fractional level
print("\n[Example 1] Creating a Fractional Level")
print("-" * 70)

# For A2 affine, h^∨ = 3
# Level k = -h^∨ + p/u = -3 + 4/3 = -5/3
level = FractionalLevel(["A", 2, 1], p=4, u=3)

print(f"Cartan type: A2~ (['A', 2, 1])")
print(f"Parameters: p=4, u=3")
print(f"Level k = {level.level} = {float(level.level):.4f}")
print(f"k + h^∨ = {level.k_plus_h_vee}")
print(f"Dual Coxeter number h^∨ = {level.h_vee}")
print(f"Lacety ℓ = {level.lacety}")

# Example 2: Create fractional weights
print("\n[Example 2] Creating Fractional Weights")
print("-" * 70)

ws = FractionalWeightSpace(["A", 2, 1])

# Create fractional weight: 3/4*Lambda[0] + 1/2*Lambda[1]
weight1 = ws.create_fractional_weight({0: (3, 4), 1: (1, 2)})
print(f"Weight 1: {weight1}")

# Create another fractional weight
weight2 = ws.create_fractional_weight({0: 1, 1: (2, 3), 2: (1, 3)})
print(f"Weight 2: {weight2}")

# Example 3: Check admissibility
print("\n[Example 3] Checking Admissible Weights")
print("-" * 70)

# Test several weights for admissibility
test_weights = [
    ({0: 2, 1: 1, 2: 0}, "2*Lambda[0] + Lambda[1]"),
    ({0: 1, 1: 1, 2: 1}, "Lambda[0] + Lambda[1] + Lambda[2]"),
    ({0: (3, 2), 1: 1, 2: 0}, "3/2*Lambda[0] + Lambda[1]"),
]

for coeffs, desc in test_weights:
    weight = ws.create_fractional_weight(coeffs)
    aw = AdmissibleWeight(["A", 2, 1], weight, level)
    is_adm = aw.is_admissible()
    status = "✓ Admissible" if is_adm else "✗ Not admissible"
    print(f"{status}: {desc}")

# Example 4: Different Cartan types
print("\n[Example 4] Different Cartan Types")
print("-" * 70)

types_to_test = [
    (["A", 1, 1], "A1~ (sl(2)^"),
    (["B", 2, 1], "B2~ (so(5)^"),
    (["G", 2, 1], "G2~ (exceptional)"),
]

for ct, desc in types_to_test:
    level = FractionalLevel(ct, p=4, u=3)
    print(f"{desc}: k = {level.level}, h^∨ = {level.h_vee}")

# Example 5: Level constraints validation
print("\n[Example 5] Level Constraints Validation")
print("-" * 70)

# Valid level
try:
    level_valid = FractionalLevel(["A", 2, 1], p=5, u=3)
    print(f"✓ Valid: p=5, u=3 (coprime), k = {level_valid.level}")
except ValueError as e:
    print(f"✗ Failed: {e}")

# Invalid: p and u not coprime
try:
    level_invalid = FractionalLevel(["A", 2, 1], p=4, u=2)
    print(f"✗ Should have failed: p=4, u=2 (not coprime)")
except ValueError as e:
    print(f"✓ Correctly rejected: {e}")

# Invalid: u not coprime with lacety (for B-type, lacety=2)
try:
    level_invalid2 = FractionalLevel(["B", 2, 1], p=5, u=2)
    print(f"✗ Should have failed: B-type with u=2 (lacety=2)")
except ValueError as e:
    print(f"✓ Correctly rejected: {e}")

# Summary
print("\n" + "=" * 70)
print("Summary")
print("=" * 70)
print("""
pyw provides:
1. FractionalLevel: for k = -h^∨ + p/u level calculations
2. FractionalWeightSpace: for creating fractional weights
3. AdmissibleWeight: for checking Kac-Wakimoto admissibility conditions
4. Support for all affine Cartan types (A, B, C, D, E, F, G)

See the documentation for more advanced features!
""")
