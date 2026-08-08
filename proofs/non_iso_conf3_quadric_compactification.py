#!/usr/bin/env python3
"""Projective compactification check for the D=4 quadric arrangement.

Translate x3=0 and compactify (a,b) in A^4 x A^4 inside P^4 x P^4 with
coordinates

  A=[A0:A1:A2:A3:A4],  B=[B0:B1:B2:B3:B4].

The affine equations q(a), q(b), q(a-b) homogenize to

  QA  = sum_i Ai^2
  QB  = sum_i Bi^2
  QAB = sum_i (Ai*B0 - Bi*A0)^2.

Boundary divisors are A0=0 and B0=0.

Dupont's theorem assumes smooth hypersurfaces locally arranged like
hyperplanes.  This script checks the first obstruction: the projective closures
of these affine quadric cones are singular.
"""

from __future__ import annotations

import sympy as sp


def gradient(poly: sp.Expr, variables: list[sp.Symbol]) -> list[sp.Expr]:
    return [sp.diff(poly, var) for var in variables]


def main() -> None:
    A0, A1, A2, A3, A4 = sp.symbols("A0 A1 A2 A3 A4")
    B0, B1, B2, B3, B4 = sp.symbols("B0 B1 B2 B3 B4")
    Avec = [A1, A2, A3, A4]
    Bvec = [B1, B2, B3, B4]
    variables = [A0, A1, A2, A3, A4, B0, B1, B2, B3, B4]

    QA = sum(ai**2 for ai in Avec)
    QB = sum(bi**2 for bi in Bvec)
    QAB = sum((ai * B0 - bi * A0) ** 2 for ai, bi in zip(Avec, Bvec))

    grad_QA = gradient(QA, variables)
    grad_QB = gradient(QB, variables)
    grad_QAB = gradient(QAB, variables)

    # QA has singular projective point [1:0:0:0:0] in the A-factor.
    origin_A_patch = {A0: 1, A1: 0, A2: 0, A3: 0, A4: 0}
    assert sp.simplify(QA.subs(origin_A_patch)) == 0
    assert all(sp.simplify(g.subs(origin_A_patch)) == 0 for g in grad_QA)

    # QB has the analogous singular point in the B-factor.
    origin_B_patch = {B0: 1, B1: 0, B2: 0, B3: 0, B4: 0}
    assert sp.simplify(QB.subs(origin_B_patch)) == 0
    assert all(sp.simplify(g.subs(origin_B_patch)) == 0 for g in grad_QB)

    # QAB is singular along the projective diagonal Ai*B0 = Bi*A0.
    diagonal_patch = {A0: 1, B0: 1, B1: A1, B2: A2, B3: A3, B4: A4}
    assert sp.simplify(QAB.subs(diagonal_patch)) == 0
    assert all(sp.simplify(g.subs(diagonal_patch)) == 0 for g in grad_QAB)

    print("non_iso_conf3_quadric_compactification.py: compactification obstruction checked")
    print("QA =", QA)
    print("QB =", QB)
    print("QAB =", sp.expand(QAB))
    print("QA singular at affine A-origin in P4; QB similarly.")
    print("QAB singular along the projective diagonal A_i B0 = B_i A0.")
    print("Conclusion: direct Dupont hypersurface-arrangement theorem needs a blow-up/resolution layer.")


if __name__ == "__main__":
    main()
