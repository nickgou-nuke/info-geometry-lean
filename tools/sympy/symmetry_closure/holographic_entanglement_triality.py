#!/usr/bin/env python3
"""SymPy shadow for `HolographicEntanglementSymmetry.lean`.

Lean owners:
  lean/InfoGeometry/Canonical/HolographicEntanglementSymmetry.lean
  lean/InfoGeometry/Holography/HolographicEntanglementSymmetry.lean

Finite shadow:
  Sector-blind entropy/area readouts are invariant under a 3-cycle, and the
  two-state entropy at `p = 1/2` is `log 2`.
"""

from __future__ import annotations

import sympy as sp

from common import check, matrix_eq, scalar_eq


def run() -> None:
    print("HolographicEntanglementSymmetry finite shadow")
    cycle = sp.Matrix([[0, 0, 1], [1, 0, 0], [0, 1, 0]])
    entropy = sp.Matrix([sp.symbols("S"), sp.symbols("S"), sp.symbols("S")])
    area = sp.Matrix([sp.symbols("A"), sp.symbols("A"), sp.symbols("A")])
    p = sp.Rational(1, 2)
    two_state_entropy = -(p * sp.log(p) + (1 - p) * sp.log(1 - p))
    newton = sp.Rational(1, 4)

    check("triality cycle has order 3", matrix_eq(cycle**3, sp.eye(3)))
    check("sector entropy is cycle-invariant", matrix_eq(cycle * entropy, entropy))
    check("sector area is cycle-invariant", matrix_eq(cycle * area, area))
    check("two-state entropy is log 2", scalar_eq(two_state_entropy, sp.log(2)))
    check("RT bookkeeping at G=1/4", scalar_eq(sp.log(2) / (4 * newton), sp.log(2)))


if __name__ == "__main__":
    run()
