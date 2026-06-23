#!/usr/bin/env python3
"""Exact-rational certificate for the de Rham/symplectic/KK/colimit bridge."""

import json
import sympy as sp


def main() -> None:
    q = sp.Rational

    # de Rham chain on an oriented triangle:
    # Ω⁰ --d0→ Ω¹ --d1→ Ω², with d1*d0 = 0.
    d0 = sp.Matrix([[-1, 1, 0], [0, -1, 1], [1, 0, -1]])
    d1 = sp.Matrix([[1, 1, 1]])
    assert d1 * d0 == sp.zeros(1, 3)

    potential = sp.Matrix([q(2), q(-1), q(3)])
    exact_current = d0 * potential
    assert d1 * exact_current == sp.zeros(1, 1)

    # Non-exact closed current on the circle complex with no face boundary.
    d1_zero = sp.zeros(1, 3)
    obstruction = sp.Matrix([q(1), q(1), q(1)])
    assert d1_zero * obstruction == sp.zeros(1, 1)
    a, b, c = sp.symbols("a b c")
    sol = sp.solve(list(d0 * sp.Matrix([a, b, c]) - obstruction), [a, b, c], dict=True)
    assert sol == []

    # Symplectic preservation: S^T J S = J.
    J = sp.Matrix([[0, 1], [-1, 0]])
    S = sp.Matrix([[1, 1], [0, 1]])
    assert S.T * J * S == J

    # Concrete 5D Kaluza-Klein block determinant.
    kk = sp.Matrix([
        [q(-1, 2), q(1, 3), 0, 0, 1],
        [q(1, 3), q(11, 9), 0, 0, q(2, 3)],
        [0, 0, 1, 0, 0],
        [0, 0, 0, 1, 0],
        [1, q(2, 3), 0, 0, 2],
    ])
    assert kk.det() == q(-2)

    # Prequantum scaling: F * hbar = omega.
    omega, curvature, hbar = q(6), q(2), q(3)
    assert curvature * hbar == omega

    # Sequential colimit cone sample: bond(x)=2x, toLimit(n,x)=x/2^n.
    n = 2
    x = q(3, 5)
    bond_x = 2 * x
    assert bond_x / (2 ** (n + 1)) == x / (2 ** n)

    print(json.dumps({
        "certificate": "de_rham_symplectic_kk_quantization_limit",
        "ring": "QQ",
        "d1_d0_zero": True,
        "exact_current_closed": True,
        "closed_nonexact_circle_current": [1, 1, 1],
        "symplectic_shear_preserves_J": True,
        "kk_metric_det": str(kk.det()),
        "prequantum_curvature_hbar": str(curvature * hbar),
        "colimit_cone_sample": True,
    }, sort_keys=True))


if __name__ == "__main__":
    main()
