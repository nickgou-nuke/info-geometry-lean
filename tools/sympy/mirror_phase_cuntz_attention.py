#!/usr/bin/env python3
"""
SymPy witness for the finite Mirror Phase Cuntz attention row/operator.

This mirrors `InfoGeometry.LLM.MirrorPhaseCuntzAttention`: the exact two-branch
attention row has weights (1/2, 1/2), sums to one, has zero row defect, matches
the depth-one dyadic KMS cylinder weights, and the corresponding 2x2 averaging
operator is a stochastic idempotent projection that preserves total branch
mass, kills the finite branch anomaly `right - left`, and fixes exactly balanced
branch vectors.
"""

from __future__ import annotations

import sympy as sp


def cylinder_kms_weight(word: tuple[bool, ...]) -> sp.Rational:
    """Uniform dyadic KMS cylinder weight 2^-|word|."""
    return sp.Rational(1, 2) ** len(word)


def main() -> None:
    print("--- SymPy Twin: Mirror Phase Cuntz Attention ---")

    attention = {
        "left": sp.Rational(1, 2),
        "right": sp.Rational(1, 2),
    }

    left_kms = cylinder_kms_weight((False,))
    right_kms = cylinder_kms_weight((True,))

    print(f"attention row: {attention}")
    print(f"depth-one KMS weights: left={left_kms}, right={right_kms}")

    assert attention["left"] == left_kms
    assert attention["right"] == right_kms

    row_sum = sp.simplify(sum(attention.values()))
    defect = sp.simplify(row_sum - 1)

    print(f"row sum: {row_sum}")
    print(f"exactness defect: {defect}")

    assert row_sum == 1
    assert defect == 0
    assert all(w >= 0 for w in attention.values())

    # Finite 2x2 attention operator: every query averages left/right branches.
    M = sp.Matrix([[sp.Rational(1, 2), sp.Rational(1, 2)],
                   [sp.Rational(1, 2), sp.Rational(1, 2)]])
    left, right = sp.symbols("left right")
    v = sp.Matrix([left, right])
    averaged = sp.simplify(M * v)
    anomaly = sp.simplify(averaged[1] - averaged[0])
    total_preservation_defect = sp.simplify(sum(averaged) - (left + right))
    fixed_point_residual = sp.simplify(averaged - v)
    fixed_point_balanced_residual = sp.simplify(
        fixed_point_residual.subs(right, left)
    )

    print(f"attention matrix M: {M}")
    print(f"row sums: {[sum(M.row(i)) for i in range(2)]}")
    print(f"M^2 - M: {sp.simplify(M * M - M)}")
    print(f"M*[left,right]^T: {averaged}")
    print(f"total preservation defect: {total_preservation_defect}")
    print(f"post-attention branch anomaly: {anomaly}")
    print(f"fixed-point residual: {fixed_point_residual}")
    print(f"balanced fixed-point residual: {fixed_point_balanced_residual}")

    assert all(sum(M.row(i)) == 1 for i in range(2))
    assert all(M[i, j] >= 0 for i in range(2) for j in range(2))
    assert sp.simplify(M * M - M) == sp.zeros(2)
    assert averaged == sp.Matrix([(left + right) / 2, (left + right) / 2])
    assert total_preservation_defect == 0
    assert anomaly == 0
    assert fixed_point_residual == sp.Matrix([(right - left) / 2, (left - right) / 2])
    assert fixed_point_balanced_residual == sp.zeros(2, 1)

    print("[SUCCESS] finite dyadic attention row/operator matches the Lean proofs.")


if __name__ == "__main__":
    main()
