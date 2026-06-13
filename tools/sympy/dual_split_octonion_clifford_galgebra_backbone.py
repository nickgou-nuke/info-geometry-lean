#!/usr/bin/env python3
"""Clifford/galgebra backbone checks for the dual split-octonion lane.

This is not a classification theorem.  It checks the exact algebraic scaffolding
used by the Lean owner `DualSplitOctonionAlgebra`:

* the split norm signature has a Clifford `Cl(4,4)` bookkeeping carrier;
* `dim Cl(4,4) = 2^8 = 256`;
* galgebra sees the same diagonal signature;
* the external dual generator remains square-zero in the separate dual-number
  factor and is not identified with a Clifford vector.
"""

from __future__ import annotations

from clifford import Cl
from galgebra.ga import Ga
import sympy as sp


def check_clifford_signature() -> None:
    layout, blades = Cl(4, 4, firstIdx=0)
    assert layout.gaDims == 256
    assert len(blades) == 256

    # The eight generating vectors square to the diagonal (4,4) signs.
    expected = [1, 1, 1, 1, -1, -1, -1, -1]
    for i, sign in enumerate(expected):
        v = blades[f"e{i}"]
        assert (v * v)[()] == sign


def check_galgebra_signature() -> None:
    names = "e0 e1 e2 e3 e4 e5 e6 e7"
    metric = [1, 1, 1, 1, -1, -1, -1, -1]
    ga = Ga(names, g=metric)
    basis = ga.mv()
    for v, sign in zip(basis, metric, strict=True):
        assert sp.simplify((v * v).scalar() - sign) == 0


def check_external_dual_number_factor() -> None:
    eps = sp.Matrix([[0, 1], [0, 0]])
    assert eps * eps == sp.zeros(2)
    assert sp.eye(2) * eps == eps
    assert eps * sp.eye(2) == eps


def main() -> None:
    check_clifford_signature()
    check_galgebra_signature()
    check_external_dual_number_factor()
    print("DUAL_SPLIT_OCTONION_CLIFFORD_GALGEBRA_BACKBONE_OK")
    print("clifford_dim=256")
    print("signature=(4,4)")
    print("dual_factor=external_square_zero")


if __name__ == "__main__":
    main()
