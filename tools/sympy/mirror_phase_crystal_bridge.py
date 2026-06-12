#!/usr/bin/env python3
"""SymPy twin for the finite Mirror Phase crystal bridge.

This mirrors `InfoGeometry.LLM.MirrorPhaseCrystalBridge`.

Checked here:
- the two binary crystal child weights are the exact dyadic attention row;
- the row sums to one and matches depth-one KMS cylinder weights;
- exact Mirror Phase attention is an idempotent averaging projector;
- the projector kills the real Bloch branch anomaly;
- balanced child readouts are fixed points.

Not checked here:
- trained transformer behavior;
- a completed Brillouin-zone quotient theorem;
- a topological-insulator classification.
"""

from __future__ import annotations

import sympy as sp


def main() -> None:
    print("--- SymPy Twin: Mirror Phase Crystal Bridge ---")

    half = sp.Rational(1, 2)
    child_weight = {False: half, True: half}
    kms_depth_one = {False: half, True: half}

    assert child_weight[False] + child_weight[True] == 1
    assert child_weight == kms_depth_one
    print("binary child weights = depth-one KMS attention row: OK")

    M = sp.Matrix([[half, half], [half, half]])
    assert M * M == M
    assert [sum(M.row(i)) for i in range(2)] == [1, 1]
    print("Mirror attention matrix is row-stochastic and idempotent: OK")

    left, right = sp.symbols("left right")
    v = sp.Matrix([left, right])
    projected = M * v
    anomaly = lambda x: sp.simplify(x[1] - x[0])

    assert anomaly(projected) == 0
    print("Mirror attention kills Bloch branch anomaly: OK")

    balanced = projected.subs({right: left})
    original_balanced = v.subs({right: left})
    assert balanced == original_balanced
    print("balanced Bloch child readout is fixed: OK")

    print("[SUCCESS] finite Mirror Phase crystal bridge verified.")


if __name__ == "__main__":
    main()
