#!/usr/bin/env python3
"""SymPy shadow for `KKTClosureSymmetry.lean`.

Lean owner:
  lean/InfoGeometry/Canonical/KKTClosureSymmetry.lean

Finite shadow:
  A concrete centralizer of a generator packet `(GammaS, GammaG, QD, HD, ZD)`.
  Diagonal units with matching paired entries preserve the packet under
  conjugation, and are closed under product and inverse.
"""

from __future__ import annotations

import sympy as sp

from common import anticommutator, check, commutator, matrix_eq


def conj(unit: sp.Matrix, operator: sp.Matrix) -> sp.Matrix:
    return unit * operator * unit.inv()


def preserves_packet(unit: sp.Matrix, packet: list[sp.Matrix]) -> bool:
    return all(matrix_eq(conj(unit, operator), operator) for operator in packet)


def run() -> None:
    print("KKTClosureSymmetry finite shadow")
    u, v, a, b = sp.symbols("u v a b", nonzero=True)
    U = sp.diag(u, v, u, v)
    V = sp.diag(a, b, a, b)
    gamma_s = sp.diag(1, 1, -1, -1)
    gamma_g = sp.diag(1, -1, 1, -1)
    qd = sp.Matrix(
        [
            [0, 0, 1, 0],
            [0, 0, 0, 1],
            [1, 0, 0, 0],
            [0, 1, 0, 0],
        ]
    )
    hd = qd * qd
    zd = gamma_s * gamma_g
    packet = [gamma_s, gamma_g, qd, hd, zd]

    check("U preserves generator packet", preserves_packet(U, packet))
    check("V preserves generator packet", preserves_packet(V, packet))
    check("U*V preserves generator packet", preserves_packet(U * V, packet))
    check("U inverse preserves generator packet", preserves_packet(U.inv(), packet))
    check(
        "conjugation transports commutator",
        matrix_eq(conj(U, commutator(gamma_s, qd)), commutator(conj(U, gamma_s), conj(U, qd))),
    )
    check(
        "odd-odd anticommutator is preserved",
        matrix_eq(conj(U, anticommutator(qd, qd)), anticommutator(qd, qd)),
    )


if __name__ == "__main__":
    run()
