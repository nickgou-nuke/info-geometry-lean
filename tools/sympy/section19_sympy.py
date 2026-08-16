#!/usr/bin/env python3
"""Repaired Section 19: finite Cl(4,C) generator checks.

This mirrors ``lean/InfoGeometry/Section19.lean``.

Closed finite checks:

* build four 4x4 complex generators from the already-used Dirac gamma matrices:
  E0 = i gamma0, E1 = gamma1, E2 = gamma2, E3 = gamma3;
* verify every generator squares to -I;
* verify distinct generators anticommute.

Not claimed here:

* a full algebra isomorphism Cl(4,C) ~= M4(C);
* an M2(H) construction;
* real-form classification.

The source tensor-product list is not used as stated because its first and
third generators would commute rather than anticommute.
"""

from __future__ import annotations

import sys
from pathlib import Path
import sympy as sp

_REPO_ROOT = Path(__file__).resolve().parents[2]
if str(_REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(_REPO_ROOT))

from tools.sympy.common import assert_matrix_zero


def main() -> None:
    print("=" * 72)
    print("REPAIRED SECTION 19: FINITE CL(4,C) GENERATOR CHECKS")
    print("=" * 72)
    print("Scope: four 4x4 complex generators with square -I and anticommutation.")
    print("Open debt: full Cl(4,C) ~= M4(C), M2(H), and real-form classification.")

    I = sp.I
    I4 = sp.eye(4)
    gamma0 = sp.diag(1, 1, -1, -1)
    gamma1 = sp.Matrix([[0, 0, 0, 1], [0, 0, 1, 0], [0, -1, 0, 0], [-1, 0, 0, 0]])
    gamma2 = sp.Matrix([[0, 0, 0, -I], [0, 0, I, 0], [0, I, 0, 0], [-I, 0, 0, 0]])
    gamma3 = sp.Matrix([[0, 0, 1, 0], [0, 0, 0, -1], [-1, 0, 0, 0], [0, 1, 0, 0]])

    generators = [I * gamma0, gamma1, gamma2, gamma3]
    for idx, gen in enumerate(generators):
        assert_matrix_zero(gen * gen + I4, f"E{idx}^2 = -I")
    print("  generator squares verified")

    for mu in range(4):
        for nu in range(4):
            if mu == nu:
                continue
            anti = generators[mu] * generators[nu] + generators[nu] * generators[mu]
            assert_matrix_zero(anti, f"E{mu}E{nu}+E{nu}E{mu}=0")
    print("  pairwise anticommutation verified")

    # Demonstrate the repaired choice matters: I⊗iσ1 and σ3⊗iσ1 commute.
    sigma1 = sp.Matrix([[0, 1], [1, 0]])
    sigma3 = sp.Matrix([[1, 0], [0, -1]])
    bad1 = sp.kronecker_product(sp.eye(2), I * sigma1)
    bad3 = sp.kronecker_product(sigma3, I * sigma1)
    commutator = bad1 * bad3 - bad3 * bad1
    assert_matrix_zero(commutator, "source first/third tensor-product generators commute")
    if bad1 * bad3 + bad3 * bad1 == sp.zeros(4):
        raise AssertionError("source tensor-product pair unexpectedly anticommutes")
    print("  source tensor-product sign issue detected and avoided")

    print("=" * 72)
    print("[SUCCESS] Section 19 theorem-safe finite checks verified.")
    print("=" * 72)


if __name__ == "__main__":
    main()
