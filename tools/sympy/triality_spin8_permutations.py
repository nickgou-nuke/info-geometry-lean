#!/usr/bin/env python3
"""Triality seed permutation witness on the boundary sector triad.

This script verifies the explicit 3-cycle sector permutation used as the
Cl(5,5) boundary-triality proxy:

- sector 0: vector-type commutator seed
- sector 1: spinor+ seed (``u + v``)
- sector 2: spinor- seed (``u - v``)

It checks the 3-cycle action and the corresponding `S3`-shape generator
`(0 1 2)`, encoded as a 3x3 permutation matrix.
"""

import sympy as sp


def chk(name: str, claim: bool, ok: list[str], fail: list[str]) -> None:
    if claim:
        ok.append(name)
    else:
        fail.append(name)


def perm_action(P: sp.Matrix, e: sp.Matrix) -> sp.Matrix:
    return P * e


def basis_vec(i: int) -> sp.Matrix:
    if i == 0:
        return sp.Matrix([1, 0, 0])
    elif i == 1:
        return sp.Matrix([0, 1, 0])
    else:
        return sp.Matrix([0, 0, 1])


def basis_index(v: sp.Matrix) -> int:
    """Extract the index of the basis vector represented by one-hot integer row."""
    vals = [int(v[i, 0]) for i in range(v.rows)]
    for j, val in enumerate(vals):
        if val == 1:
            return j
    return -1


print("=== Triality 3-cycle witness ===")

P = sp.Matrix([[0, 0, 1],
               [1, 0, 0],
               [0, 1, 0]])
I3 = sp.eye(3)

checks_ok: list[str] = []
checks_fail: list[str] = []

chk("P^3 = I3", P**3 == I3, checks_ok, checks_fail)
chk("P^0 = I3", P**0 == I3, checks_ok, checks_fail)
chk("P^2 ≠ I3", P**2 != I3, checks_ok, checks_fail)

# Sector labels as 3-vectors.
sector_names = ["vector", "spinor+", "spinor-"]

print("=== 3-cycle action on sector basis ===")
for i, name in enumerate(sector_names):
    img = perm_action(P, basis_vec(i))
    j = basis_index(img)
    print(f"  {name:8} ↦ {sector_names[j]}")

chk("vector maps to spinor+",
    basis_index(perm_action(P, basis_vec(0))) == 1,
    checks_ok, checks_fail)
chk("spinor+ maps to spinor-",
    basis_index(perm_action(P, basis_vec(1))) == 2,
    checks_ok, checks_fail)
chk("spinor- maps to vector",
    basis_index(perm_action(P, basis_vec(2))) == 0,
    checks_ok, checks_fail)

print("=== Finite-cycle closure ===")
for name in ("vector", "spinor+", "spinor-"):
    print(f"  {name}")

print(f"\nOVERALL: {len(checks_ok)} checks passed, {len(checks_fail)} failed")
if checks_fail:
    print("FAILED:", checks_fail)
else:
    print("checks:", checks_ok)
