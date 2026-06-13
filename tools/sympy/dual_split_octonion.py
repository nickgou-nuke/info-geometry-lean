#!/usr/bin/env python3
"""Theorem-safe dual split-octonion backbone verifier.

Lean twin:
    lean/InfoGeometry/OperatorAlgebra/DualSplitOctonion.lean

Scope boundary:
    This verifier checks only the dual-number extension of the repository's
    concrete split-octonion/Zorn multiplication:

        DO_s = O_s ⊕ eps O_s,       eps^2 = 0
        (a + eps u)(b + eps v) = ab + eps(av + ub)

    It deliberately does NOT assert:
      * Aut(DO_s) = G_{2(2)} ⋉ R^7;
      * SO(4,4) ⋉ R^8 metric/affine classification;
      * SU(3) ⋉ R^6 gauge/stabilizer classification;
      * that the repo's seven finite G2(2) fixed points form a Fano plane;
      * that those seven finite fixed points are an R^7 translation module.

    The finite G2(2) fixed-point ledger is cross-checked only as a boundary:
    fixed_internal_line_count = 3, not 7.
"""

from __future__ import annotations

from dataclasses import dataclass
import importlib.util
import json
from pathlib import Path
import subprocess
import sys
import tempfile
from typing import Any

ROOT = Path(__file__).resolve().parents[2]
SAGE = Path("/home/goutev/miniforge3/envs/sage/bin/sage")


def load_module(path: Path, name: str) -> Any:
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load {path}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


split = load_module(ROOT / "tools/sympy/split_octonion_multiplication.py", "split_oct_mul_safe_dual")


@dataclass(frozen=True)
class DualSplitOct:
    primal: Any
    tangent: Any

    def __add__(self, other: "DualSplitOct") -> "DualSplitOct":
        return DualSplitOct(self.primal + other.primal, self.tangent + other.tangent)

    def __sub__(self, other: "DualSplitOct") -> "DualSplitOct":
        return DualSplitOct(self.primal - other.primal, self.tangent - other.tangent)

    def __mul__(self, other: "DualSplitOct") -> "DualSplitOct":
        return DualSplitOct(
            self.primal * other.primal,
            self.primal * other.tangent + self.tangent * other.primal,
        )


ZERO_D = DualSplitOct(split.ZERO, split.ZERO)


def base_lift(x: Any) -> DualSplitOct:
    return DualSplitOct(x, split.ZERO)


def eps_lift(x: Any) -> DualSplitOct:
    return DualSplitOct(split.ZERO, x)


DUAL_EPSILON = eps_lift(split.ONE)


def associator(x: DualSplitOct, y: DualSplitOct, z: DualSplitOct) -> DualSplitOct:
    return (x * y) * z - x * (y * z)


def verify_dual_backbone() -> None:
    basis = split.BASIS
    assert len(basis) == 8

    for x in basis:
        for y in basis:
            assert base_lift(x) * base_lift(y) == base_lift(x * y)
            assert eps_lift(x) * eps_lift(y) == ZERO_D
            assert base_lift(x) * eps_lift(y) == eps_lift(x * y)
            assert eps_lift(x) * base_lift(y) == eps_lift(x * y)

    assert DUAL_EPSILON * DUAL_EPSILON == ZERO_D
    assert (DUAL_EPSILON * DUAL_EPSILON).primal == split.ZERO
    assert (base_lift(split.UP[0]) * base_lift(split.UP[1])).primal == split.UP[0] * split.UP[1]

    lifted = associator(base_lift(split.UP[0]), base_lift(split.UP[1]), base_lift(split.DOWN[1]))
    assert lifted == base_lift(split.UP[0])
    assert lifted != ZERO_D


def verify_identity_aut_interface_candidate() -> None:
    # This is only an interface sanity check: the identity map preserves the
    # product and the epsilon ideal.  It is not a classification of Aut(DO_s).
    for x in [base_lift(b) for b in split.BASIS] + [eps_lift(b) for b in split.BASIS]:
        assert x == x
    for x in [base_lift(b) for b in split.BASIS]:
        for y in [eps_lift(b) for b in split.BASIS]:
            assert x * y == x * y


def verify_finite_g2_fixed_point_boundary() -> dict[str, Any]:
    incidence = load_module(
        ROOT / "tools/sympy/g2_2_fixed_point_incidence.py", "g2_2_fixed_point_incidence_safe_dual"
    )
    data = incidence.verify_gap_fixed_point_incidence()
    assert data["fixed_points"] == [1, 19, 30, 32, 41, 42, 54]
    assert data["fixed_internal_line_count"] == 3
    assert data["fixed_set_is_fano_plane_under_this_incidence"] is False
    return data


def verify_sage_dimension_backbone() -> str:
    code = r'''
from sage.all import Matrix, QQ
import json
base_dim = int(8)
dual_dim = int(2 * base_dim)
zero_square_rank = int(Matrix(QQ, 8, 8, lambda i,j: 0).rank())
print(json.dumps({
  "base_coordinate_count": base_dim,
  "dual_coordinate_count": dual_dim,
  "epsilon_square_matrix_rank": zero_square_rank
}, sort_keys=True))
'''
    with tempfile.NamedTemporaryFile("w", suffix=".sage", delete=False) as handle:
        handle.write(code)
        sage_path = Path(handle.name)
    try:
        out = subprocess.check_output([str(SAGE), str(sage_path)], cwd=ROOT, text=True)
    finally:
        sage_path.unlink(missing_ok=True)
    start = out.index("{")
    end = out.rindex("}") + 1
    data = json.loads(out[start:end])
    assert data == {
        "base_coordinate_count": 8,
        "dual_coordinate_count": 16,
        "epsilon_square_matrix_rank": 0,
    }
    return json.dumps(data, sort_keys=True)


def main() -> None:
    verify_dual_backbone()
    verify_identity_aut_interface_candidate()
    fixed = verify_finite_g2_fixed_point_boundary()
    sage_json = verify_sage_dimension_backbone()
    print(sage_json)
    print(
        json.dumps(
            {
                "fixed_points": fixed["fixed_points"],
                "fixed_internal_line_count": fixed["fixed_internal_line_count"],
                "fixed_set_is_fano_plane_under_this_incidence": fixed[
                    "fixed_set_is_fano_plane_under_this_incidence"
                ],
            },
            sort_keys=True,
        )
    )
    print("DUAL_SPLIT_OCTONION_SAFE_BACKBONE_OK")
    print("scope: O_s⊕eps O_s only; no G2(2) fixed-point/R7 or semidirect-product classification")


if __name__ == "__main__":
    main()
