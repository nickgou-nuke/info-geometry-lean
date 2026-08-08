#!/usr/bin/env python3
"""
SymPy witness for FibAnyonThm1: Fibonacci fusion rules.
Verifies: φ² = φ + 1, τ² = τ + 1, φ + τ = 1, φ·τ = -1
"""
import sympy as sp

φ = (1 + sp.sqrt(5))/2
τ = (1 - sp.sqrt(5))/2

checks = [
    ("φ² = φ + 1", sp.simplify(φ**2 - φ - 1)),
    ("τ² = τ + 1", sp.simplify(τ**2 - τ - 1)),
    ("φ + τ = 1", sp.simplify(φ + τ - 1)),
    ("φ·τ = -1", sp.simplify(φ*τ + 1)),
    ("1/φ = -τ", sp.simplify(1/φ + τ)),
    ("1/τ = -φ", sp.simplify(1/τ + φ)),
]

all_pass = True
for name, diff in checks:
    ok = diff == 0
    print(f"  {'✅' if ok else '❌'} {name}: {diff}")
    if not ok: all_pass = False

print(f"\n{'✅ All golden ratio identities verified.' if all_pass else '❌ Verification failed.'}")
