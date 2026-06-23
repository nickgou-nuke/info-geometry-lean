#!/usr/bin/env python3
"""
Compute the five-grade weight mapping for the O(5,5) construction
as described in InfoGeometry.Canonical.O55FiveGradeCapstone.
Outputs a JSON dictionary mapping generator names to their integer weights.
"""

import json

# Based on the proved adjoint actions:
#   [D, u5] = u5   => weight +1
#   [D, u4] = u4   => weight +1
# Expected by symmetry (marked as sorry in Lean):
#   [D, v5] = -v5  => weight -1
#   [D, v4] = -v4  => weight -1
# D5, D4, D have weight 0 (they commute with D up to scalar? actually [D, D5]=0)
# J5, J4, J have weight 0 (they anticommute with D? Actually theta flips sign,
# but under ad D they have weight 0 because [D, J] = 0? We'll follow the capstone.)

weights = {
    "u5": 1,
    "v5": -1,
    "u4": 1,
    "v4": -1,
    "D5": 0,
    "D4": 0,
    "D": 0,
    "J5": 0,
    "J4": 0,
    "J": 0,
}

print(json.dumps(weights, indent=2))