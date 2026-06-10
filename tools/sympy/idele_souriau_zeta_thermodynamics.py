#!/usr/bin/env python3
"""Three-layer idele -> Souriau zeta thermodynamics bridge.

SymPy shadow of
`InfoGeometry.Arithmetic.IdeleSouriauZetaThermodynamics`.

It verifies only the theorem-safe algebraic corridor already present in the
repo:

* three-layer idele shadow = (log scale, finite arithmetic unit, Fourier parity);
* induced chart action uses only log scale + Fourier parity;
* arithmetic layer acts on cyclotomic exponents, not on centered chart points;
* the displacement Souriau partition / Massieu potential are invariant under the
  induced chart action.

No full adelic quotient, full Bost-Connes KMS classification, spectral
realization of zeros, or RH claim is made here.
"""

from __future__ import annotations

from dataclasses import dataclass
import math
import sympy as sp

u, v, u1, v1, u2, v2, L, M = sp.symbols("u v u1 v1 u2 v2 L M", real=True)

Point = tuple[sp.Expr, sp.Expr]


def assert_zero(expr: sp.Expr, label: str) -> None:
    if sp.simplify(expr) != 0:
        raise AssertionError((label, sp.factor(expr)))


def units_mod(m: int) -> list[int]:
    return [a for a in range(1, m) if math.gcd(a, m) == 1]


def inv_mod(a: int, m: int) -> int:
    for b in units_mod(m):
        if (a * b) % m == 1:
            return b
    raise ValueError((a, m))


def critical_mirror(p: Point) -> Point:
    return (-p[0], p[1])


def height_translation(t: sp.Expr, p: Point) -> Point:
    return (p[0], p[1] + t)


def flat_displacement(p: Point, q: Point) -> sp.Expr:
    return (p[0] - q[0]) ** 2 + (p[1] - q[1]) ** 2


def same(p: Point, q: Point) -> bool:
    return all(sp.simplify(a - b) == 0 for a, b in zip(p, q, strict=True))


@dataclass(frozen=True)
class ThreeLayerIdele:
    log_scale: sp.Expr
    arithmetic_unit: int
    modulus: int
    parity: str  # "id" or "dual"

    def chart_act(self, p: Point) -> Point:
        base = p if self.parity == "id" else critical_mirror(p)
        return height_translation(self.log_scale, base)

    def arithmetic_act(self, exponent: int) -> int:
        if self.parity == "id":
            unit = self.arithmetic_unit
        else:
            unit = inv_mod(self.arithmetic_unit, self.modulus)
        return (unit * exponent) % self.modulus


def displacement_partition(beta: Point, moments: list[Point]) -> sp.Expr:
    total: sp.Expr = sp.Integer(0)
    for m in moments:
        total += sp.exp(-flat_displacement(beta, m))
    return sp.simplify(total)


def displacement_massieu(beta: Point, moments: list[Point]) -> sp.Expr:
    return sp.log(displacement_partition(beta, moments))


def main() -> None:
    modulus = 5
    units = units_mod(modulus)
    assert units == [1, 2, 3, 4]

    A = ThreeLayerIdele(L, 2, modulus, "id")
    B = ThreeLayerIdele(M, 3, modulus, "dual")

    x = (u, v)
    m1 = (u1, v1)
    m2 = (u2, v2)
    beta = (u, v)

    # Chart action uses only log scale + parity.
    assert same(A.chart_act(x), (u, v + L))
    assert same(B.chart_act(x), (-u, v + M))

    # Arithmetic layer acts on cyclotomic exponents, not on chart points.
    assert A.arithmetic_act(1) == 2
    assert B.arithmetic_act(1) == inv_mod(3, modulus)
    assert same(B.chart_act(x), height_translation(M, critical_mirror(x)))

    # Dual parity fixed locus on centered chart is u = 0.
    fixed_u = sp.solve(sp.Eq(critical_mirror(x)[0], x[0]), u)
    assert fixed_u == [0]

    # Displacement energy invariance under the induced chart action.
    for element in (A, B):
        assert_zero(
            flat_displacement(element.chart_act(beta), element.chart_act(m1))
            - flat_displacement(beta, m1),
            f"displacement energy invariance {element.parity}",
        )
        assert_zero(
            flat_displacement(element.chart_act(beta), element.chart_act(m2))
            - flat_displacement(beta, m2),
            f"displacement energy invariance 2 {element.parity}",
        )

    # Finite displacement partition and Massieu invariance.
    moments = [m1, m2]
    for element in (A, B):
        moved_moments = [element.chart_act(m) for m in moments]
        moved_beta = element.chart_act(beta)
        z_original = displacement_partition(beta, moments)
        z_moved = displacement_partition(moved_beta, moved_moments)
        assert_zero(z_moved - z_original, f"partition invariance {element.parity}")

        phi_original = displacement_massieu(beta, moments)
        phi_moved = displacement_massieu(moved_beta, moved_moments)
        assert_zero(phi_moved - phi_original, f"massieu invariance {element.parity}")

    print("idele_souriau_zeta_thermodynamics: ok")
    print("  three_layer_shadow: (R_+^* log scale, finite Zhat^* quotient, Fourier Z2)")
    print("  chart_action: (logScale, parity) -> height translation + critical mirror")
    print("  arithmetic_lane: cyclotomic exponent action separated from chart action")
    print("  fixed_locus_dual: u = 0")
    print("  displacement_massieu: invariant under induced chart action")


if __name__ == "__main__":
    main()
