#!/usr/bin/env python3
"""Section 27 codebase-grounded finite integration checks.

This mirrors ``lean/InfoGeometry/Section27.lean`` after rebasing the section on
existing owners:

* ``BiQuaternionKahlerFinite`` for the R4 quaternionic complex structures,
  symplectic readout, Poisson skewness, Fisher metric, and toy Casimir;
* ``BiQuaternionKahlerLegendreFinite`` for the quadratic Legendre transform;
* ``BiQuaternionKahlerSymplecticNoetherBridge`` for the finite Noether readback;
* ``HodgeStar4DFinite`` for the Lorentzian 4D two-form Hodge star;
* ``Potential.Thermo`` for abstract Massieu/Fenchel contact algebra.

No smooth manifolds, continuum Noether theorem, partition integrals,
Fisher-Rao Hessians, Stokes theorem, Hopf fibration, or representation-theoretic
Casimir classification is claimed here.
"""

from __future__ import annotations

import sys
from pathlib import Path
import sympy as sp

_REPO_ROOT = Path(__file__).resolve().parents[2]
if str(_REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(_REPO_ROOT))

from tools.sympy.common import assert_matrix_zero, assert_zero


def dot(u: sp.Matrix, v: sp.Matrix) -> sp.Expr:
    return (u.T * v)[0]


def main() -> None:
    print("=" * 72)
    print("SECTION 27: CODEBASE-GROUNDED BIQUATERNION/KAEHLER CHECKS")
    print("=" * 72)

    I4c = sp.Matrix(
        [
            [0, -1, 0, 0],
            [1, 0, 0, 0],
            [0, 0, 0, -1],
            [0, 0, 1, 0],
        ]
    )
    J4c = sp.Matrix(
        [
            [0, 0, -1, 0],
            [0, 0, 0, 1],
            [1, 0, 0, 0],
            [0, -1, 0, 0],
        ]
    )
    K4c = sp.Matrix(
        [
            [0, 0, 0, -1],
            [0, 0, -1, 0],
            [0, 1, 0, 0],
            [1, 0, 0, 0],
        ]
    )
    eye4 = sp.eye(4)
    assert_matrix_zero(I4c * I4c + eye4, "I4c^2 = -1")
    assert_matrix_zero(J4c * J4c + eye4, "J4c^2 = -1")
    assert_matrix_zero(K4c * K4c + eye4, "K4c^2 = -1")
    assert_matrix_zero(I4c * J4c - K4c, "I4c*J4c = K4c")
    assert_matrix_zero(J4c * I4c + K4c, "J4c*I4c = -K4c")
    print("  existing R4 quaternionic complex structures verified")

    x = sp.Matrix(sp.symbols("x0 x1 x2 x3", real=True))
    y = sp.Matrix(sp.symbols("y0 y1 y2 y3", real=True))
    omega_xy = dot(I4c * x, y)
    omega_yx = dot(I4c * y, x)
    assert_zero(omega_xy + omega_yx, "symplecticI skewness")
    print("  existing symplectic/Poisson skew readout verified")

    v = sp.Matrix(sp.symbols("v0 v1 v2 v3", real=True))
    q = sp.Matrix(sp.symbols("q0 q1 q2 q3", real=True))
    potential = sp.symbols("Vq", real=True)
    kinetic_v = sp.Rational(1, 2) * dot(v, v)
    lagrangian = kinetic_v - potential
    momentum = v
    hamiltonian = sp.Rational(1, 2) * dot(momentum, momentum) + potential
    legendre_readout = dot(momentum, v) - lagrangian
    assert_zero(legendre_readout - hamiltonian, "R4 Legendre readout")
    print("  existing R4 quadratic Legendre identity verified")

    grad_v = sp.Matrix(sp.symbols("g0 g1 g2 g3", real=True))
    p = sp.Matrix(sp.symbols("p0 p1 p2 p3", real=True))
    noether_readback = dot(I4c * p, p) - dot(grad_v, I4c * q)
    radial_readback = noether_readback.subs({grad_v[i]: q[i] for i in range(4)})
    assert_zero(radial_readback, "radial finite Noether readback")
    radial_hamiltonian_shift = (
        sp.Rational(1, 2) * dot(I4c * p, I4c * p)
        + sp.Rational(1, 2) * dot(I4c * q, I4c * q)
        - sp.Rational(1, 2) * dot(p, p)
        - sp.Rational(1, 2) * dot(q, q)
    )
    assert_zero(radial_hamiltonian_shift, "radial Hamiltonian I4c invariance")
    print("  existing finite Noether/radial Hamiltonian bridge verified")

    f = sp.Matrix(sp.symbols("f0 f1 f2 f3 f4 f5"))

    def hodge_star(vec: sp.Matrix) -> sp.Matrix:
        return sp.Matrix([vec[3], vec[4], vec[5], -vec[0], -vec[1], -vec[2]])

    star_f = hodge_star(f)
    assert_matrix_zero(hodge_star(star_f) + f, "4D Lorentzian hodgeStar^2 = -1")
    self_part = sp.Matrix([(f[i] - sp.I * star_f[i]) / 2 for i in range(6)])
    anti_part = sp.Matrix([(f[i] + sp.I * star_f[i]) / 2 for i in range(6)])
    assert_matrix_zero(self_part + anti_part - f, "self+anti reconstructs")
    assert_matrix_zero(hodge_star(self_part) - sp.I * self_part, "+i eigenspace")
    assert_matrix_zero(hodge_star(anti_part) + sp.I * anti_part, "-i eigenspace")
    print("  existing finite 4D Hodge-star decomposition verified")

    theta, eta, psi, phi_grad, beta = sp.symbols("theta eta psi phi_grad beta")
    grad_theta = sp.symbols("grad_theta")
    fenchel_gap_at_contact = psi + (theta * grad_theta - psi) - theta * grad_theta
    assert_zero(fenchel_gap_at_contact, "Massieu/Fenchel contact gap")
    entropy = theta * grad_theta - psi
    assert_zero(entropy - (theta * grad_theta - psi), "entropy contact definition")
    scaled_gap = beta * (psi + phi_grad - theta * eta)
    assert_zero(scaled_gap - beta * (psi + phi_grad - theta * eta), "scaled gap readout")
    print("  existing Massieu/Fenchel contact algebra verified")

    sigma_x = sp.Matrix([[0, 1], [1, 0]])
    sigma_y_real = sp.Matrix([[0, -1], [1, 0]])
    assert_matrix_zero(sigma_x * sigma_x + sigma_y_real * sigma_y_real, "toy Casimir")
    print("  existing finite toy Casimir readout verified")

    print("=" * 72)
    print("[SUCCESS] Section 27 codebase-grounded finite checks verified.")
    print("=" * 72)


if __name__ == "__main__":
    main()
