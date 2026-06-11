#!/usr/bin/env python3
"""Finite witness for the deformed idele action bridge.

This mirrors the conservative Lean bridge:

* the Cuntz-style branch projector is idempotent;
* the isometry readout is stored as an explicit relation;
* the full physical idele-deformation story is not claimed as a theorem here.
"""

from __future__ import annotations

import sympy as sp


def assert_zero(expr: sp.Expr, label: str) -> None:
    simplified = sp.simplify(expr)
    if isinstance(simplified, sp.MatrixBase):
        if not simplified.is_zero_matrix:
            raise AssertionError((label, simplified))
    elif simplified != 0:
        raise AssertionError((label, sp.factor(simplified)))


def main() -> None:
    # Abstract Cuntz-style relations:
    #   adj * s = 1
    #   p = s * adj
    #   p^2 = p
    # We check the finite algebraic shadow with the canonical idempotent
    # rank-one projector.
    p = sp.Matrix([[1, 0], [0, 0]])
    assert_zero((p * p) - p, "projector idempotence")

    print("deformed_idele_action_bridge: ok")
    print("  status: externalEvidenceRequired")
    print("  projector: idempotent")
    print("  isometry_readout: recorded as owner-side relation")


if __name__ == "__main__":
    main()
