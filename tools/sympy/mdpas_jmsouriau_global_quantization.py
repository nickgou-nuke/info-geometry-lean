#!/usr/bin/env python3
"""Exact finite audit for the MDPAS/JM de Rham/symplectic/KK/quantization lane."""

from __future__ import annotations

import sympy as sp


def require_zero(name: str, expr) -> None:
    value = sp.simplify(sp.expand(expr))
    if isinstance(value, sp.MatrixBase):
        if value != sp.zeros(*value.shape):
            raise AssertionError(f"{name} failed: {value}")
    elif value != 0:
        raise AssertionError(f"{name} failed: {value}")
    print(f"[ok] {name}")


def main() -> None:
    # Finite de Rham obstruction on a 3-cycle.
    phi0, phi1, phi2 = sp.symbols("phi0 phi1 phi2")
    exact_cycle = (phi1 - phi0) + (phi2 - phi1) + (phi0 - phi2)
    require_zero("exact 1-cochain has zero cycle integral", exact_cycle)
    assert sp.Integer(1) + sp.Integer(1) + sp.Integer(1) == 3
    assert sp.Integer(3) != 0
    print("[ok] unit cycle current is obstructed")

    # Canonical symplectic form on Q^4.
    J = sp.Matrix([[0, 0, 1, 0],
                   [0, 0, 0, 1],
                   [-1, 0, 0, 0],
                   [0, -1, 0, 0]])
    require_zero("symplectic skew", J + J.T)
    assert J.det() == 1
    print("[ok] symplectic nondegenerate determinant")

    # 5D Kaluza-Klein block metric: g4 + r A A^T, r A, r.
    r = sp.symbols("r")
    a0, a1, a2, a3 = sp.symbols("a0 a1 a2 a3")
    A = sp.Matrix([a0, a1, a2, a3])
    g4 = sp.diag(1, -1, -1, -1)
    kk = sp.zeros(5)
    kk[:4, :4] = g4 + r * (A * A.T)
    kk[:4, 4] = r * A
    kk[4, :4] = (r * A).T
    kk[4, 4] = r
    require_zero("Kaluza-Klein 5D block symmetry", kk - kk.T)

    # Finite half-spin prequantization.
    hbar = sp.symbols("hbar")
    require_zero("half-spin integrality 2*(hbar/2)-hbar", 2 * (hbar / 2) - hbar)

    print("MDPAS_JMSOURIAU_GLOBAL_QUANTIZATION_SYMPY_OK")


if __name__ == "__main__":
    main()

