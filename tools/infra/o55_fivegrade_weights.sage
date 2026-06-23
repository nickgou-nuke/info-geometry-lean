#!/usr/bin/env sage -python
# -*- coding: utf-8 -*-
"""
SageMath script to output the O(5,5) five-grade weight mapping.
This mirrors the Python/SymPy version and can be extended to compute
the weights from a Clifford algebra construction if desired.
"""

import json

# The weight mapping derived from the O(5,5) closure-by-commutators:
#   [D, u5] =  u5  => weight +1
#   [D, u4] =  u4  => weight +1
#   [D, v5] = -v5  => weight -1  (expected)
#   [D, v4] = -v4  => weight -1  (expected)
#   D5, D4, D, J5, J4, J have weight 0
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