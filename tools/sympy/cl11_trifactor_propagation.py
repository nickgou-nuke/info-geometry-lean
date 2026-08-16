#!/usr/bin/env python3
"""
Finite Cl(1,1) matrix-stage trifactor propagation witness.

Mirrors lean/InfoGeometry/Clifford/Cl11TrifactorPropagation.lean using the
finite embedding A |-> A ⊗ I_2.  This does not construct an infinite Clifford
algebra or prove a universal Bott-periodicity isomorphism.
"""

import sys
from pathlib import Path
import sympy as sp

_REPO_ROOT = Path(__file__).resolve().parents[2]
if str(_REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(_REPO_ROOT))

from tools.sympy.common import assert_matrix_eq, assert_zero


def embed(a: sp.Matrix) -> sp.Matrix:
    return sp.kronecker_product(a, sp.eye(2))


def propagate(n: int, p: sp.Matrix) -> sp.Matrix:
    out = p
    for _ in range(n):
        out = embed(out)
    return out


def normalized_trace(stage: int, a: sp.Matrix) -> sp.Expr:
    return sp.simplify(sp.trace(a) / (sp.Integer(2) ** stage))


def main() -> None:
    print("=" * 72)
    print("CL(1,1) TRIFACTOR PROPAGATION -- FINITE SYMPY VERIFICATION")
    print("=" * 72)

    projector = sp.Matrix([[1, 0], [0, 0]])
    tripotent = sp.Matrix([[1, 0], [0, -1]])

    assert_matrix_eq(projector * projector, projector, "base idempotent")
    assert_matrix_eq(tripotent * tripotent * tripotent, tripotent, "base tripotent")

    for n in range(5):
        p_n = propagate(n, projector)
        t_n = propagate(n, tripotent)
        stage = n + 1

        assert_matrix_eq(p_n * p_n, p_n, f"idempotent propagation stage {stage}")
        assert_matrix_eq(t_n * t_n * t_n, t_n, f"tripotent propagation stage {stage}")
        assert_zero(
            normalized_trace(stage, p_n) - normalized_trace(1, projector),
            f"normalized trace projector stage {stage}",
        )
        assert_zero(
            normalized_trace(stage, t_n) - normalized_trace(1, tripotent),
            f"normalized trace tripotent stage {stage}",
        )

    print("  idempotent propagation verified through finite stages")
    print("  tripotent propagation verified through finite stages")
    print("  normalized trace stability verified through finite stages")
    print("=" * 72)
    print("CL(1,1) TRIFACTOR PROPAGATION VERIFIED")
    print("=" * 72)


if __name__ == "__main__":
    main()
