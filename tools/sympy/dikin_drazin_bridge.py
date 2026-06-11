#!/usr/bin/env python3
"""Finite Dikin/Drazin bridge witness.

Mirrors `InfoGeometry.Canonical.DikinDrazinBridge`.

It verifies the finite algebraic shadow:

* a tripotent `M` has idempotent core projector `P_core = M^2`;
* `P_core + P_null = I`;
* a positive Hessian metric is strictly positive on nonzero core vectors.

No self-concordance, cone containment theorem, or analytic Dikin ellipsoid
result is asserted here.
"""

from __future__ import annotations

import sympy as sp


def assert_matrix_eq(left: sp.Matrix, right: sp.Matrix, label: str) -> None:
    diff = sp.simplify(left - right)
    if diff != sp.zeros(*left.shape):
        raise AssertionError(f"{label} failed:\n{diff}")


def main() -> None:
    M = sp.diag(1, -1, 0)
    H = sp.diag(2, 3, 5)
    I = sp.eye(3)

    p_core = M * M
    p_null = I - p_core

    assert_matrix_eq(M**3, M, "M^3 = M")
    assert_matrix_eq(p_core * p_core, p_core, "P_core^2 = P_core")
    assert_matrix_eq(p_core + p_null, I, "P_core + P_null = I")
    assert_matrix_eq(M * p_null, sp.zeros(3), "M P_null = 0")

    for v in [sp.Matrix([1, 0, 0]), sp.Matrix([0, 1, 0]), sp.Matrix([1, 2, 9])]:
        core_v = p_core * v
        if core_v != sp.zeros(3, 1):
            q = (core_v.T * H * core_v)[0]
            assert sp.simplify(q) > 0

    print("dikin_drazin_bridge: PASS")
    print("  tripotent core projector is idempotent")
    print("  null projector completes identity")
    print("  positive Hessian readout is stable on nonzero core vectors")


if __name__ == "__main__":
    main()

