#!/usr/bin/env python3
"""SymPy shadow for `SplitTrialityKernel.lean`.

Lean owner:
  lean/InfoGeometry/Quantum/SplitTrialityKernel.lean

Finite shadow:
  The real doubled two-channel kernel with nilpotent left/right maps,
  complementary recompositions, and an involutive triality supercharge.
"""

from __future__ import annotations

import sympy as sp

from common import anticommutator, check, matrix_eq


def run() -> None:
    print("SplitTrialityKernel finite shadow")
    left = sp.Matrix([[0, 0], [1, 0]])
    right = sp.Matrix([[0, 1], [0, 0]])
    p_plus = right * left
    p_minus = left * right
    q = left + right
    k_axis = p_plus - p_minus

    check("left channel is nilpotent", matrix_eq(left * left, sp.zeros(2)))
    check("right channel is nilpotent", matrix_eq(right * right, sp.zeros(2)))
    check("right∘left = Pplus", matrix_eq(right * left, p_plus))
    check("left∘right = Pminus", matrix_eq(left * right, p_minus))
    check("Pplus + Pminus = I", matrix_eq(p_plus + p_minus, sp.eye(2)))
    check("triality supercharge square is I", matrix_eq(q * q, sp.eye(2)))
    check("square equals odd-odd anticommutator", matrix_eq(q * q, anticommutator(left, right)))
    check("phase axis anticommutes with supercharge", matrix_eq(q * k_axis, -k_axis * q))


if __name__ == "__main__":
    run()
