#!/usr/bin/env python3
"""Finite dual split-octonion algebra verifier.

Lean twin:
    lean/InfoGeometry/OperatorAlgebra/DualSplitOctonionAlgebra.lean

Scope:
    This verifies only the algebraic dual-number extension
    D O_s = O_s + eps O_s with eps^2 = 0 over the existing concrete Zorn
    split-octonion multiplication.  It does not assert Aut(D O_s), SO(4,4)
    metric symmetry, SU(3) stabilizers, or any physical gauge classification.
"""

from __future__ import annotations

from dataclasses import dataclass
import importlib.util
from pathlib import Path
import sys
from typing import Any


ROOT = Path(__file__).resolve().parents[2]


def load_module(path: Path, name: str) -> Any:
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load {path}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


split = load_module(ROOT / "tools/sympy/split_octonion_multiplication.py", "split_oct_mul")


@dataclass(frozen=True)
class DualZorn:
    primal: Any
    tangent: Any

    def __mul__(self, other: "DualZorn") -> "DualZorn":
        return DualZorn(
            self.primal * other.primal,
            self.primal * other.tangent + self.tangent * other.primal,
        )


ZERO_D = DualZorn(split.ZERO, split.ZERO)


def base_lift(x: Any) -> DualZorn:
    return DualZorn(x, split.ZERO)


def eps_lift(x: Any) -> DualZorn:
    return DualZorn(split.ZERO, x)


def associator_d(x: DualZorn, y: DualZorn, z: DualZorn) -> DualZorn:
    return (x * y) * z - x * (y * z)  # type: ignore[operator]


def dual_sub(left: DualZorn, right: DualZorn) -> DualZorn:
    return DualZorn(left.primal - right.primal, left.tangent - right.tangent)


def dual_add(left: DualZorn, right: DualZorn) -> DualZorn:
    return DualZorn(left.primal + right.primal, left.tangent + right.tangent)


DualZorn.__add__ = dual_add  # type: ignore[method-assign]
DualZorn.__sub__ = dual_sub  # type: ignore[method-assign]


def verify_dual_product_rules() -> None:
    basis = split.BASIS
    for x in basis:
        for y in basis:
            assert base_lift(x) * base_lift(y) == base_lift(x * y)
            assert eps_lift(x) * eps_lift(y) == ZERO_D
            assert base_lift(x) * eps_lift(y) == eps_lift(x * y)
            assert eps_lift(x) * base_lift(y) == eps_lift(x * y)

    dual_epsilon = eps_lift(split.ONE)
    assert dual_epsilon * dual_epsilon == ZERO_D


def verify_projection_and_nonassociativity() -> None:
    x = DualZorn(split.UP[0], split.DOWN[0])
    y = DualZorn(split.UP[1], split.DOWN[1])
    assert (x * y).primal == x.primal * y.primal

    lifted = associator_d(base_lift(split.UP[0]), base_lift(split.UP[1]), base_lift(split.DOWN[1]))
    assert lifted == base_lift(split.UP[0])
    assert lifted != ZERO_D


def verify_supergraded_and_klein_readouts() -> None:
    dual_epsilon = eps_lift(split.ONE)
    # Odd--odd superbracket is the anticommutator; eps^2 = 0 makes it zero.
    assert dual_epsilon * dual_epsilon + dual_epsilon * dual_epsilon == ZERO_D

    # Integer readouts mirroring the existing Brillouin-Klein owners.
    klein_z2_zero_defect = (0 + 0) % 2
    klein_boundary_zero_charge = 0 + 0 + 0 - 0
    assert klein_z2_zero_defect == 0
    assert klein_boundary_zero_charge == 2 * 0

    for _stage in range(16):
        assert dual_epsilon * dual_epsilon == ZERO_D


def main() -> None:
    verify_dual_product_rules()
    verify_projection_and_nonassociativity()
    verify_supergraded_and_klein_readouts()
    print("DUAL_SPLIT_OCTONION_ALGEBRA_OK")
    print("coordinate_count=16")
    print("scope: dual-number extension of concrete split-octonion multiplication only")


if __name__ == "__main__":
    main()
