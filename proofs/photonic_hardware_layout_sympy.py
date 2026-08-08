#!/usr/bin/env python3
"""SymPy witness for photonic hardware KAN layout."""

from __future__ import annotations

import sympy as sp


def assert_zero(name: str, expr) -> None:
    residue = expr.applyfunc(sp.simplify) if isinstance(expr, sp.MatrixBase) else sp.simplify(expr)
    ok = residue == sp.zeros(*residue.shape) if isinstance(residue, sp.MatrixBase) else residue == 0
    print(f"{name}: {'PASS' if ok else 'FAIL'}")
    if not ok:
        print(residue)
        raise SystemExit(1)


def main() -> int:
    th, a, g = sp.symbols("theta alpha gamma", real=True)
    K = sp.Matrix([[sp.cos(th), -sp.sin(th)], [sp.sin(th), sp.cos(th)]])
    A = sp.diag(sp.exp(a), sp.exp(-a))
    N = sp.Matrix([[1, g], [0, 1]])
    cell = sp.simplify(K * A * N)
    expected = sp.Matrix([
        [sp.exp(a) * sp.cos(th), g * sp.exp(a) * sp.cos(th) - sp.exp(-a) * sp.sin(th)],
        [sp.exp(a) * sp.sin(th), g * sp.exp(a) * sp.sin(th) + sp.exp(-a) * sp.cos(th)],
    ])
    assert_zero("hardware cell = KAN transfer", cell - expected)
    assert_zero("det MZI=1", K.det() - 1)
    assert_zero("det GainLoss=1", A.det() - 1)
    assert_zero("det Nilpotent=1", N.det() - 1)
    assert_zero("det hardware cell=1", cell.det() - 1)

    m12, m21, m22 = cell[0, 1], cell[1, 0], cell[1, 1]
    S = sp.simplify((1 / m22) * sp.Matrix([[1, -m12], [m21, cell.det()]]))
    assert_zero("hardware transmission reciprocity", S[0, 0] - S[1, 1])
    print("OK photonic hardware layout SymPy witness completed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
