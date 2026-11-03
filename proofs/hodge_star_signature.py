#!/usr/bin/env python3
"""Word-model census for `InfoGeometry.Algebra.HodgeStarSignatureFour`.

Certifies the explicit 6x6 Hodge stars on the exterior-square carrier of a
4-slot basis `e0, e1, e2` (spatial) / `e3` (time), `eta = diag(1, 1, 1, -1)`
(Pauli Sec. 4 Eq. (2), time slot last).

Basis order (the `Set.powersetCard` order of
`CliffordFourExteriorGradeBridge.degreeBasis 2`, pairs lexicographic):
    b0 = e0^e1, b1 = e0^e2, b2 = e0^e3, b3 = e1^e2, b4 = e1^e3, b5 = e2^e3

Lorentz star `S_L = *eta`, Euclidean star `S_E = *delta` (column j holds the
coefficients of `*b_j` in the row basis):

  Archaic defining property (verified per column *and* per star):
    alpha ^ (star alpha) = <alpha, alpha> vol, using the 2-form Gram
    diag(+1, +1, -1, +1, -1, -1) for eta and +1s for delta.

  (L1) S_L + S_L^T = 0                    anti-self-transpose (Lorentz)
  (L2) S_L @ S_L = -I6                    star-star = sgn(det eta) = -1
  (L3) S_L^T @ Gr @ S_L = -Gr             star anti-isometry, s = -1 side
  (L4) Diag(S_L) = 0, trace = 0, det = +1
  (E1) S_E - S_E^T = 0                    symmetric (Euclidean star)
  (E2) S_E @ S_E = +I6                    star-star = sgn(det delta) = +1
  (E3) P± = (I ± S_E)/2 form the self-dual / anti-self-dual packet:
       P± @ P± = P±, P₊ @ P₋ = 0, P₊ + P₋ = I6, P± symmetric, trace P± = 3.

The Lorentz star admits *no* real ±1 eigendecomposition: (L2) forbids the
`(1 ± *eta)/2` proector packet on real forms (square would need *eta^2 +1).
The packet is therefore stated here in the Euclidean section only, exactly
as in the Lean carrier.

Strict mode: any failure exits 1.
"""
from __future__ import annotations

import itertools
import sys

import sympy as sp

PAIRS = [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]

I6 = sp.eye(6)
GR = sp.diag(1, 1, -1, 1, -1, -1)   # eta's action on the 2-form carrier
GR_E = sp.eye(6)                    # delta's

HODGE_L = sp.Matrix([
    [0, 0, 0, 0, 0, -1],
    [0, 0, 0, 0, 1, 0],
    [0, 0, 0, 1, 0, 0],
    [0, 0, -1, 0, 0, 0],
    [0, -1, 0, 0, 0, 0],
    [1, 0, 0, 0, 0, 0],
])

HODGE_E = sp.Matrix([
    [0, 0, 0, 0, 0, 1],
    [0, 0, 0, 0, -1, 0],
    [0, 0, 0, 1, 0, 0],
    [0, 0, 1, 0, 0, 0],
    [0, -1, 0, 0, 0, 0],
    [1, 0, 0, 0, 0, 0],
])


def wedge_sign(p: tuple[int, int], q: tuple[int, int]) -> int:
    """Sign of e_p ^ e_q against vol = e0^e1^e2^e3; 0 when slots overlap."""
    slots = list(p) + list(q)
    if len(set(slots)) != 4:
        return 0
    order = sorted(slots)
    inversions = 0
    for a, b in itertools.combinations(range(4), 2):
        if slots.index(order[a]) > slots.index(order[b]):
            inversions += 1
    return -1 if inversions % 2 else 1


def wedge_matrix(p: tuple[int, int], s: sp.Matrix, j: int, gram: sp.Matrix) -> sp.Expr:
    """alpha_p ^ (star alpha_j) for the s-column j, as (coefficient of vol)."""
    total = sp.Integer(0)
    for k, q in enumerate(PAIRS):
        coefficient = s[k, j]
        if coefficient == 0:
            continue
        total += coefficient * wedge_sign(p, q)
    return total


def must(cond: bool, tag: str, failures: list[str]) -> None:
    if cond:
        print(f"  [OK]      {tag}")
    else:
        print(f"  [FAIL]    {tag}")
        failures.append(tag)


def must_matrix(mat: sp.Matrix, expected: sp.Matrix, tag: str, failures: list[str]) -> None:
    if sp.simplify(mat - expected) == sp.zeros(*mat.shape):
        print(f"  [OK]      {tag}")
    else:
        print(f"  [FAIL]    {tag}")
        failures.append(tag)


def defining_property_ok(s: sp.Matrix, gram: sp.Matrix, tag: str, failures: list[str]) -> None:
    """Per-column check of alpha_j ^ (star alpha_j) = <alpha_j, alpha_j> vol."""
    problems: list[str] = []
    for j, (i1, i2) in enumerate(PAIRS):
        # alpha_j ^ (star alpha_j): the coefficient of vol:
        lhs = wedge_matrix((i1, i2), s, j, gram)
        # b_j ^ vol = <alpha, alpha> vol means lhs should equal gram[j, j]
        if sp.simplify(lhs - gram[j, j]) != 0:
            problems.append(f"column {j} ({i1},{i2}): {lhs} != {gram[j, j]}")
    if problems:
        print(f"  [FAIL]    {tag}: {problems}")
        failures.append(tag)
    else:
        print(f"  [OK]      {tag}")


def main() -> int:
    failures: list[str] = []
    print("hodge_star_signature census (strict):")

    print("  Lorentz * on lambda2:")
    defining_property_ok(HODGE_L, GR, "(L0) defining wedge property, all 6 columns", failures)
    must_matrix(HODGE_L + HODGE_L.T, sp.zeros(6),
                "(L1) hodgeLorentz + hodgeLorentz^T = 0", failures)
    must_matrix(HODGE_L * HODGE_L, -I6,
                "(L2) hodgeLorentz^2 = -I6", failures)
    must_matrix(HODGE_L.T * GR * HODGE_L, -GR,
                "(L3) hodgeLorentz^T Gr hodgeLorentz = -Gr (anti-isometry, sgn = -1)",
                failures)
    must(all(HODGE_L.diagonal()[k] == 0 for k in range(6)) and HODGE_L.trace() == 0,
         "(L4a) zero diagonal, trace zero", failures)
    must(HODGE_L.det() == 1, "(L4b) det hodgeLorentz = 1", failures)

    print("  Euclidean * on lambda2:")
    defining_property_ok(HODGE_E, GR_E, "(E0) defining wedge property, all 6 columns", failures)
    must_matrix(HODGE_E - HODGE_E.T, sp.zeros(6),
                "(E1) hodgeEuclidean is symmetric", failures)
    must_matrix(HODGE_E * HODGE_E, I6,
                "(E2) hodgeEuclidean^2 = I6", failures)
    must_matrix(HODGE_E.T * GR_E * HODGE_E, GR_E,
                "(E2b) hodgeEuclidean^T Gr hodgeEuclidean = Gr (isometry, sgn = +1)",
                failures)

    print("  Euclidean self-dual packet P± = (I ± S)/2:")
    pp = (I6 + HODGE_E) / 2
    pm = (I6 - HODGE_E) / 2
    must_matrix(pp * pp, pp, "(E3a) P+ idempotent", failures)
    must_matrix(pm * pm, pm, "(E3b) P- idempotent", failures)
    must_matrix(pp * pm, sp.zeros(6), "(E3c) P+ P- = 0", failures)
    must_matrix(pp + pm, I6, "(E3d) P+ + P- = I6", failures)
    must_matrix(pp - pp.T, sp.zeros(6), "(E3e) P+ symmetric", failures)
    must_matrix(pm - pm.T, sp.zeros(6), "(E3f) P- symmetric", failures)
    must(pp.trace() == 3 and pm.trace() == 3, "(E3g) traces P± = 3", failures)

    total = 17
    passed = total - len(failures)
    print(f"\n{passed}/{total} checks passed; failures: {failures or 'none'}")
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
