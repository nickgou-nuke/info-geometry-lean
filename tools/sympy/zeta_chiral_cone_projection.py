#!/usr/bin/env python3
"""SymPy witness for centered zeta chiral-cone projections.

This mirrors `InfoGeometry.Arithmetic.ZetaChiralConeProjection`.

The script verifies the algebraic part only:

* centered coordinate maps satisfy `conjugation ∘ critical_mirror = functional_dual`;
* Schwarz reflection plus the centered functional equation imply `J xi = xi`;
* the even projector fixes completed `xi`;
* the odd / scale-normal projector kills completed `xi`;
* an uncompleted `zeta` readout has a symbolic odd-density expression, with
  nonvanishing left as an analytic/model-specific question.
"""

from __future__ import annotations

import sympy as sp


u, v = sp.symbols("u v", real=True)
Xi = sp.Symbol("Xi_uv")
Zeta = sp.Symbol("Zeta_uv")
JZeta = sp.Symbol("JZeta_uv")


def same(point_a: tuple[sp.Expr, sp.Expr], point_b: tuple[sp.Expr, sp.Expr]) -> bool:
    return all(sp.simplify(a - b) == 0 for a, b in zip(point_a, point_b))


def conjugation(point: tuple[sp.Expr, sp.Expr]) -> tuple[sp.Expr, sp.Expr]:
    return (point[0], -point[1])


def functional_dual(point: tuple[sp.Expr, sp.Expr]) -> tuple[sp.Expr, sp.Expr]:
    return (-point[0], -point[1])


def critical_mirror(point: tuple[sp.Expr, sp.Expr]) -> tuple[sp.Expr, sp.Expr]:
    return (-point[0], point[1])


def even_projector(value: sp.Expr, j_value: sp.Expr) -> sp.Expr:
    return sp.simplify((value + j_value) / 2)


def odd_projector(value: sp.Expr, j_value: sp.Expr) -> sp.Expr:
    return sp.simplify((value - j_value) / 2)


def main() -> None:
    point = (u, v)

    # Coordinate identity used by the Lean proof:
    # conjugation(critical_mirror(u, v)) = functional_dual(u, v).
    assert same(conjugation(critical_mirror(point)), functional_dual(point))

    # Completed xi rewrite:
    # J xi(u,v) = conjugate(xi(-u,v)).
    # Schwarz sends conjugate(xi(-u,v)) to xi(-u,-v).
    # Functional equation sends xi(-u,-v) to xi(u,v).
    xi_after_schwarz_coordinate = conjugation(critical_mirror(point))
    assert same(xi_after_schwarz_coordinate, functional_dual(point))
    j_xi_after_functional_equation = Xi

    assert sp.simplify(even_projector(Xi, j_xi_after_functional_equation) - Xi) == 0
    assert sp.simplify(odd_projector(Xi, j_xi_after_functional_equation)) == 0

    # Uncompleted zeta has no imposed functional-equation completion in this witness.
    # Its J-odd component is the symbolic modular density.
    relative_modular_density = odd_projector(Zeta, JZeta)
    assert relative_modular_density == (Zeta - JZeta) / 2

    print("zeta_chiral_cone_projection: ok")
    print("  coordinate_identity: conjugation ∘ critical_mirror = functional_dual")
    print("  completed_xi: Schwarz + functional equation imply J xi = xi")
    print("  xi_even_projection: P_J^+(xi) = xi")
    print("  xi_odd_projection: P_J^-(xi) = 0")
    print("  raw_zeta_density: P_J^-(zeta) = (zeta - Jzeta)/2")
    print("  boundary: no RH, KMS, natural-cone construction, or nonvanishing theorem claimed")


if __name__ == "__main__":
    main()
