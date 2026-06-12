#!/usr/bin/env python3
"""
SymPy witness for `InfoGeometry.Clifford.InductiveColimitCrystal`.

Finite atom binding is modeled by the Kronecker embedding A |-> A ⊗ I₂.  The
script checks the finite identities mirrored by Lean: normalized trace stability,
raw determinant squaring, normalized log-det stability, square-zero/idempotent
transport, and commutator transport.
"""

from __future__ import annotations

import sympy as sp


def bind(a: sp.Matrix) -> sp.Matrix:
    """One finite crystal binding step: A ↦ A ⊗ I₂."""
    return sp.kronecker_product(a, sp.eye(2))


def normalized_trace(a: sp.Matrix) -> sp.Expr:
    return sp.simplify(sp.trace(a) / a.rows)


def normalized_logdet_symbolic(det_expr: sp.Expr, dim: int) -> sp.Expr:
    """Formal normalized log|det| readout used only for the squaring check."""
    return sp.log(sp.Abs(det_expr)) / dim


def commutator(k: sp.Matrix, x: sp.Matrix) -> sp.Matrix:
    return sp.simplify(k * x - x * k)


def main() -> None:
    print("--- SymPy Twin: Inductive Colimit Crystal ---")

    a, b, c, d, e, f, g, h = sp.symbols("a b c d e f g h")
    A = sp.Matrix([[a, b], [c, d]])
    K = sp.Matrix([[e, f], [g, h]])
    P = sp.Matrix([[1, 0], [0, 0]])
    N = sp.Matrix([[0, 1], [0, 0]])

    A_bind = bind(A)
    K_bind = bind(K)
    P_bind = bind(P)
    N_bind = bind(N)

    trace_residual = sp.simplify(normalized_trace(A_bind) - normalized_trace(A))
    det_square_residual = sp.simplify(A_bind.det() - A.det() ** 2)

    # Since det(A ⊗ I₂) = det(A)^2 and dim doubles, normalized logdet is stable
    # at the formal positive determinant level.
    detA = sp.symbols("detA", positive=True)
    logdet_residual = sp.simplify(
        normalized_logdet_symbolic(detA**2, 4) - normalized_logdet_symbolic(detA, 2)
    )

    commutator_residual = sp.simplify(bind(commutator(K, A)) - commutator(K_bind, A_bind))
    idempotent_residual = sp.simplify(P_bind * P_bind - P_bind)
    square_zero_residual = sp.simplify(N_bind * N_bind)

    print(f"normalized trace residual: {trace_residual}")
    print(f"det(A⊗I₂) - det(A)^2: {det_square_residual}")
    print(f"normalized logdet residual: {logdet_residual}")
    print(f"commutator transport residual: {commutator_residual}")
    print(f"idempotent transport residual: {idempotent_residual}")
    print(f"square-zero transport residual: {square_zero_residual}")

    assert trace_residual == 0
    assert det_square_residual == 0
    assert logdet_residual == 0
    assert commutator_residual == sp.zeros(4)
    assert idempotent_residual == sp.zeros(4)
    assert square_zero_residual == sp.zeros(4)

    print("[SUCCESS] finite atom binding identities match the Lean crystal readout.")


if __name__ == "__main__":
    main()
