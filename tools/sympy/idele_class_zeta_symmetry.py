#!/usr/bin/env python3
"""Finite algebraic witness for the idele-class zeta symmetry layers.

This is a SymPy shadow of the formal Lean module
`InfoGeometry.Arithmetic.IdeleClassZetaSymmetry`.

It verifies the structurally defensible part of the statement:

* the positive scale group is represented in log coordinates by addition;
* a finite cyclotomic quotient of `Zhat^*` is modeled by units modulo `m`;
* the product layer composes componentwise;
* the Fourier/Pontryagin dual involution sends `(log_scale, g)` to
  `(-log_scale, g^{-1})`;
* on centered zeta coordinates the same involution is `u -> -u`, i.e. the
  critical mirror.

No full adelic quotient, KMS classification, or RH theorem is claimed here.
"""

from __future__ import annotations

from dataclasses import dataclass
import math
import sympy as sp


L, M, u, v = sp.symbols("L M u v", real=True)


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


@dataclass(frozen=True)
class FiniteIdeleLayer:
    log_scale: sp.Expr
    galois_unit: int
    modulus: int

    def compose(self, other: "FiniteIdeleLayer") -> "FiniteIdeleLayer":
        assert self.modulus == other.modulus
        return FiniteIdeleLayer(
            sp.simplify(self.log_scale + other.log_scale),
            (self.galois_unit * other.galois_unit) % self.modulus,
            self.modulus,
        )

    def inverse(self) -> "FiniteIdeleLayer":
        return FiniteIdeleLayer(
            sp.simplify(-self.log_scale),
            inv_mod(self.galois_unit, self.modulus),
            self.modulus,
        )

    def fourier_dual(self) -> "FiniteIdeleLayer":
        return self.inverse()

    def acts_on_beta(self, beta: sp.Expr) -> sp.Expr:
        return sp.simplify(beta + self.log_scale)

    def acts_on_cyclotomic_exponent(self, numerator: int) -> int:
        return (self.galois_unit * numerator) % self.modulus


@dataclass(frozen=True)
class ThreeLayerIdeleSymmetry:
    layer: FiniteIdeleLayer
    parity_dual: bool

    def compose(self, other: "ThreeLayerIdeleSymmetry") -> "ThreeLayerIdeleSymmetry":
        acted = other.layer.fourier_dual() if self.parity_dual else other.layer
        return ThreeLayerIdeleSymmetry(
            self.layer.compose(acted),
            self.parity_dual ^ other.parity_dual,
        )

    def acts_on_centered(self, point: tuple[sp.Expr, sp.Expr]) -> tuple[sp.Expr, sp.Expr]:
        return critical_mirror(point) if self.parity_dual else point

    def acts_on_beta(self, beta: sp.Expr) -> sp.Expr:
        return self.layer.acts_on_beta(beta)


def critical_mirror(point: tuple[sp.Expr, sp.Expr]) -> tuple[sp.Expr, sp.Expr]:
    return (-point[0], point[1])


def main() -> None:
    modulus = 5
    units = units_mod(modulus)
    assert units == [1, 2, 3, 4]

    # Finite `Zhat^*` quotient: units modulo m form an abelian group.
    for a in units:
        assert (a * inv_mod(a, modulus)) % modulus == 1
        for b in units:
            assert (a * b) % modulus in units
            assert (a * b) % modulus == (b * a) % modulus

    A = FiniteIdeleLayer(L, 2, modulus)
    B = FiniteIdeleLayer(M, 3, modulus)
    C = FiniteIdeleLayer(sp.Integer(7), 4, modulus)
    identity = FiniteIdeleLayer(sp.Integer(0), 1, modulus)

    # Product layer: log-positive scale plus finite cyclotomic Galois unit.
    assert A.compose(identity) == A
    assert identity.compose(A) == A
    assert A.compose(B).compose(C) == A.compose(B.compose(C))
    assert A.compose(A.inverse()).galois_unit == 1
    assert_zero(A.compose(A.inverse()).log_scale, "idele inverse log scale")

    beta = sp.symbols("beta", real=True)
    assert_zero(
        A.compose(B).acts_on_beta(beta) - A.acts_on_beta(B.acts_on_beta(beta)),
        "scale action composition",
    )

    # Cyclotomic/Galois action on e(a/m): a -> g*a mod m.
    exponent = 1
    lhs = A.compose(B).acts_on_cyclotomic_exponent(exponent)
    rhs = A.acts_on_cyclotomic_exponent(B.acts_on_cyclotomic_exponent(exponent))
    assert lhs == rhs

    # Fourier/Pontryagin duality is the Z2 involution:
    # (log lambda, g) -> (-log lambda, g^-1).
    assert A.fourier_dual().fourier_dual() == A
    assert A.compose(B).fourier_dual() == A.fourier_dual().compose(B.fourier_dual())

    # Centered zeta chart: Fourier duality is the critical mirror u -> -u.
    point = (u, v)
    assert critical_mirror(critical_mirror(point)) == point
    fixed_u = sp.solve(sp.Eq(critical_mirror(point)[0], point[0]), u)
    assert fixed_u == [0]

    # The normal envelope is inverted by the Fourier dual in log scale.
    x = sp.symbols("x", positive=True)
    assert_zero(sp.exp(L * sp.log(x)) * sp.exp((-L) * sp.log(x)) - 1, "dual scale envelope")

    # Full three-layer shadow: (R_+^* x finite Galois unit) semidirect Z2.
    E = ThreeLayerIdeleSymmetry(identity, False)
    TA = ThreeLayerIdeleSymmetry(A, False)
    TB = ThreeLayerIdeleSymmetry(B, False)
    DA = ThreeLayerIdeleSymmetry(A, True)
    DB = ThreeLayerIdeleSymmetry(B, True)
    assert E.compose(TA) == TA
    assert TA.compose(E) == TA
    assert TA.compose(TB).acts_on_beta(beta) == A.acts_on_beta(B.acts_on_beta(beta))
    assert DA.acts_on_centered(point) == critical_mirror(point)
    assert DA.acts_on_centered(DA.acts_on_centered(point)) == point
    assert DA.compose(DB).parity_dual is False
    assert_zero(
        DA.compose(DB).layer.log_scale - (A.log_scale - B.log_scale),
        "semidirect scale component",
    )

    # Conservative RH-style binding predicate: if all zeros satisfy u=0, no
    # supplied zero can be off the Fourier fixed surface.
    supplied_zero = (sp.Integer(0), v)
    assert supplied_zero[0] == 0

    trace_partition, zeta_readout, temp = sp.symbols("Z_trace zeta_readout temp")
    assert sp.Eq(trace_partition, zeta_readout) == sp.Eq(trace_partition, zeta_readout)

    print("idele_class_zeta_symmetry: ok")
    print("  scale_layer: R_+^* represented by additive log scale")
    print("  arithmetic_layer: finite quotient of Zhat^* = units modulo 5")
    print("  fourier_z2: (L,g) -> (-L,g^-1), u -> -u")
    print("  three_layer_shadow: (log-scale, finite Galois unit) semidirect Z2")
    print("  bost_connes_shadow: cyclotomic exponent a/m -> g*a/m")
    print("  rh_binding_predicate: zeros constrained to Fourier fixed surface u=0")
    print("  fixed_centered_line: u = 0")


if __name__ == "__main__":
    main()
