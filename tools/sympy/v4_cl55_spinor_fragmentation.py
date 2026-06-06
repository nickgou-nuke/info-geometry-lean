#!/usr/bin/env python3
"""Finite Cl(5,5)-style V₄ spinor fragmentation witness.

This script uses a concrete 2x2 real Clifford-like null-pair model
(U^2 = V^2 = 0, UV + VU = I) to represent:

- J = U - V (Clifford inversion on Cl(1,1) / Cl(5,5) slice)
- S = U + V (projective inversion / sandwich partner)
- seed sectors s₊ = U + V, s₋ = U - V
"""

import sympy as sp

# Null-pair model in a 2x2 real representation
U = sp.Matrix([[0, 1], [0, 0]])
V = sp.Matrix([[0, 0], [1, 0]])
I = sp.eye(2)

J = U - V
S = U + V

# Seed sectors in this slice
s_plus = U + V
s_minus = U - V

checks = []
def chk(name: str, claim: bool) -> None:
    if not claim:
        raise AssertionError(f"check failed: {name}")
    checks.append(name)

print("=== 1. Null-pair base checks ===")
chk("U^2 = 0", U * U == sp.zeros(2))
chk("V^2 = 0", V * V == sp.zeros(2))
chk("UV + VU = I", U * V + V * U == I)

print("=== 2. Cl(1,1) projective/Clifford elements ===")
chk("J = u - v", J == U - V)
chk("S = u + v", S == U + V)
chk("J^2 = -I", J * J == -I)
chk("S^2 = I", S * S == I)

print("=== 3. Sandwich actions ===")
chk("J u J = v", J * U * J == V)
chk("J v J = u", J * V * J == U)
chk("S u S = v", S * U * S == V)
chk("S v S = u", S * V * S == U)

print("=== 4. Spinor seed fragmentation ===")
chk("J·(s_plus)·J = s_plus", J * s_plus * J == s_plus)
chk("J·(s_minus)·J = -s_minus", J * s_minus * J == -s_minus)
chk("S·(s_plus)·S = s_plus", S * s_plus * S == s_plus)
chk("S·(s_minus)·S = -s_minus", S * s_minus * S == -s_minus)

print("=== 5. V4 (Weyl/Klein) representation checks ===")
r1 = sp.Matrix([[-1, 0], [0, 1]])
r2 = sp.Matrix([[1, 0], [0, -1]])
r12 = r1 * r2  # diag(-1,-1)

chk("Weyl r1 involution", r1 * r1 == I)
chk("Weyl r2 involution", r2 * r2 == I)
chk("Weyl r12 involution", r12 * r12 == I)

# V4 charges of seed sectors: left/right action.
# s_plus = e1 + e2 (columns basis)
# s_minus = e1 - e2.
# In this concrete basis, r1 flips the second component relative phase and r2 flips the first.
# We record the character table by direct multiplication.
charges = {
    "s_plus": (r1 * s_plus * sp.Matrix([1, 1]), r2 * s_plus * sp.Matrix([1, 1])),
    "s_minus": (r1 * s_minus * sp.Matrix([1, -1]), r2 * s_minus * sp.Matrix([1, -1])),
}
print("s_plus charge matrix actions:", charges["s_plus"])
print("s_minus charge matrix actions:", charges["s_minus"])

print("=== 6. Involution consistency checks ===")
chk("J^2 involution", J * J * J * J == I)
chk("S^2 involution", S * S * S * S == I)

print(f"\nOVERALL: {len(checks)}/{len(checks)} checks passed ✅")
print("Checks:", checks)
