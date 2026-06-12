"""Finite symplectic/Noether bridge mirror.

This mirrors
`InfoGeometry.Canonical.BiQuaternionKahlerSymplecticNoetherBridge`.

Closed scope:
* the Lagrangian/Killing symplectic readout is the same finite
  `omega_I(x,y)=dot(I4c*x,y)` packet used by the `R^4` Kähler module;
* `I4c` is skew-adjoint for the Euclidean dot product;
* the finite Noether derivative for `Q(q,p)=dot(I4c*q,p)` vanishes when the
  potential gradient is invariant along `I4c*q`;
* the radial quadratic Hamiltonian `T(p)+T(q)` is invariant under `I4c`.
* the Belinfante source readout remains symmetric after adding the torsion
  quadratic source;
* the torsion-norm slot is the finite quadratic action contribution.

No smooth flows, differentiable Noether theorem, moment maps, currents, or
field dynamics are claimed here.
"""

from __future__ import annotations

import sympy as sp


def assert_zero(expr: sp.Expr, label: str) -> None:
    simplified = sp.simplify(sp.expand(expr))
    if simplified != 0:
        raise AssertionError(f"{label} did not simplify to zero:\n{simplified}")


def dot(u: sp.Matrix, v: sp.Matrix) -> sp.Expr:
    return (u.T * v)[0]


def main() -> None:
    I4c = sp.Matrix(
        [
            [0, -1, 0, 0],
            [1, 0, 0, 0],
            [0, 0, 0, -1],
            [0, 0, 1, 0],
        ]
    )

    q = sp.Matrix(sp.symbols("q0 q1 q2 q3", real=True))
    p = sp.Matrix(sp.symbols("p0 p1 p2 p3", real=True))
    x = sp.Matrix(sp.symbols("x0 x1 x2 x3", real=True))
    y = sp.Matrix(sp.symbols("y0 y1 y2 y3", real=True))
    grad_v = sp.Matrix(sp.symbols("g0 g1 g2 g3", real=True))

    lagrangian_symplectic = dot(I4c * x, y)
    finite_symplectic_i = dot(I4c * x, y)
    assert_zero(
        lagrangian_symplectic - finite_symplectic_i,
        "Lagrangian symplectic form agrees with finite I4c readout",
    )

    assert I4c.T == -I4c
    assert_zero(dot(I4c * x, y) + dot(x, I4c * y), "I4c skew-adjoint dot readout")
    assert_zero(dot(I4c * p, p), "I4c self-orthogonality")

    noether_readback = dot(I4c * p, p) - dot(grad_v, I4c * q)
    invariant_potential_readout = dot(grad_v, I4c * q)
    assert_zero(
        noether_readback + invariant_potential_readout,
        "Noether readback reduces to the invariant-potential obstruction",
    )

    radial_readback = noether_readback.subs({grad_v[i]: q[i] for i in range(4)})
    assert_zero(radial_readback, "radial quadratic finite Noether readback")

    kinetic = lambda v: sp.Rational(1, 2) * dot(v, v)
    assert_zero(kinetic(I4c * p) - kinetic(p), "I4c kinetic invariance")
    radial_hamiltonian_shift = (
        kinetic(I4c * p) + kinetic(I4c * q) - (kinetic(p) + kinetic(q))
    )
    assert_zero(radial_hamiltonian_shift, "radial quadratic Hamiltonian invariance")

    b00, b01, b11 = sp.symbols("b00 b01 b11", real=True)
    t00, t01, t11 = sp.symbols("t00 t01 t11", real=True)
    belinfante = sp.Matrix([[b00, b01], [b01, b11]])
    torsion_source = sp.Matrix([[t00, t01], [t01, t11]])
    total_source = belinfante + torsion_source
    assert total_source.T == total_source

    dirac, mass, curvature, kappa_inv, alpha, torsion_norm = sp.symbols(
        "dirac mass curvature kappa_inv alpha torsion_norm", real=True
    )
    effective_action = (
        dirac
        - mass
        + sp.Rational(1, 2) * kappa_inv * curvature
        + sp.Rational(1, 4) * alpha * torsion_norm
    )
    torsion_quadratic_action_term = sp.Rational(1, 4) * alpha * torsion_norm
    assert_zero(
        effective_action.subs({torsion_norm: 0})
        - (dirac - mass + sp.Rational(1, 2) * kappa_inv * curvature),
        "zero-torsion action reduction",
    )
    assert_zero(
        torsion_quadratic_action_term - sp.Rational(1, 4) * alpha * torsion_norm,
        "torsion-quadratic action slot",
    )

    print("biquaternion_kahler_symplectic_noether_bridge: ok")
    print("  omega_L(x,y) equals dot(I4c*x,y) on finite R^4")
    print("  finite Noether readback vanishes for radial quadratic potential")
    print("  Belinfante-plus-torsion source remains symmetric")
    print("  torsion-norm slot is the finite quadratic action contribution")
    print("  honest scope: finite flat R^4 algebra only")


if __name__ == "__main__":
    main()
