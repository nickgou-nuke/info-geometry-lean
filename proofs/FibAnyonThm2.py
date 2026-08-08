#!/usr/bin/env python3
"""
SymPy witness for FibAnyonThm2: F-matrix for Fibonacci anyons.
Verifies: F² = I, det(F) = -1, F entries satisfy golden ratio identities.
"""
import sympy as sp

φ = (1 + sp.sqrt(5))/2

F = sp.Matrix([[1/φ, 1/sp.sqrt(φ)], [1/sp.sqrt(φ), -1/φ]])
I2 = sp.eye(2)

checks = [
    ("F² = I", sp.simplify(F*F - I2)),
    ("det(F) = -1", sp.simplify(F.det() + 1)),
    ("F is unitary", sp.simplify(F * F.T - I2)),
]

all_pass = True
for name, diff in checks:
    ok = diff == sp.zeros(*diff.shape) if hasattr(diff, 'shape') else diff == 0
    status = '✅' if ok else '❌'
    print(f"  {status} {name}")
    if not ok:
        sp.pprint(diff)
        all_pass = False

print(f"\n{'✅ F-matrix verified.' if all_pass else '❌ Verification failed.'}")
