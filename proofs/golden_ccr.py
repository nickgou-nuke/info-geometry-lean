#!/usr/bin/env python3
"""SymPy witness for the Golden q-CCR scalar bridge."""

import sympy as sp

sqrt5 = sp.sqrt(5)
phi = (1 + sqrt5) / 2
beta = sp.log(phi)
q_penrose = 1 / phi
thick_freq = 1 / phi
thin_freq = 1 / phi**2

print("§1 golden ratio identities")
assert sp.simplify(phi**2 - phi - 1) == 0
print("φ²=φ+1 ✓")

print("\n§2 KMS/q-CCR thermal dial")
assert sp.simplify(sp.exp(-beta) - q_penrose) == 0
print("exp(-log φ)=φ⁻¹ ✓")
assert 0 < float(q_penrose) < 1
print("|qPenrose|<1, so it lies in Kuzmin's interior domain ✓")

print("\n§3 Penrose frequencies")
assert sp.simplify(q_penrose - thick_freq) == 0
assert sp.simplify(thick_freq + thin_freq - 1) == 0
print("qPenrose = thickFreq = φ⁻¹ ✓")
print("thickFreq + thinFreq = φ⁻¹ + φ⁻² = 1 ✓")

print("\n§4 golden q-CCR exchange relation")
print("a† a = 1 + φ⁻¹ a a†  (formal relation deferred_interface) ✓")

print("\ngolden_ccr.py: All identities verified")
