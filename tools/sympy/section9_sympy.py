#!/usr/bin/env python3
"""Section 9: quaternion, spin, and Riemann curvature.

Exact SymPy companion to ``lean/InfoGeometry/Section9.lean``.

It verifies the finite algebraic content:

* Lorentz generators sigma_ab = (i/2)[sigma_a,sigma_b] are traceless;
* quaternion curvature is antisymmetric under mu <-> nu;
* spin curvature is antisymmetric under mu <-> nu;
* spin commutators are traceless;
* the fixed-index Riemann curvature formula is antisymmetric in mu,nu;
* the flat chain Riemann -> spin -> quaternion sends zero to zero.
"""

from __future__ import annotations

from dataclasses import dataclass

import sympy as sp


def assert_zero(name: str, expr) -> None:
    value = sp.simplify(expr)
    if value != 0:
        raise AssertionError(f"{name} failed: {value}")
    print(f"  {name}: OK")


def assert_matrix_zero(name: str, matrix: sp.Matrix) -> None:
    diff = matrix.applyfunc(sp.simplify)
    if diff != sp.zeros(*diff.shape):
        raise AssertionError(f"{name} failed:\n{diff}")
    print(f"  {name}: OK")


@dataclass(frozen=True)
class Quat:
    r: sp.Expr
    x: sp.Expr
    y: sp.Expr
    z: sp.Expr

    def tuple(self) -> tuple[sp.Expr, sp.Expr, sp.Expr, sp.Expr]:
        return (self.r, self.x, self.y, self.z)

    def __add__(self, other: "Quat") -> "Quat":
        return Quat(self.r + other.r, self.x + other.x, self.y + other.y, self.z + other.z)

    def __neg__(self) -> "Quat":
        return Quat(-self.r, -self.x, -self.y, -self.z)

    def __sub__(self, other: "Quat") -> "Quat":
        return self + (-other)

    def __mul__(self, other: "Quat") -> "Quat":
        return Quat(
            self.r * other.r - self.x * other.x - self.y * other.y - self.z * other.z,
            self.r * other.x + self.x * other.r + self.y * other.z - self.z * other.y,
            self.r * other.y - self.x * other.z + self.y * other.r + self.z * other.x,
            self.r * other.z + self.x * other.y - self.y * other.x + self.z * other.r,
        )


ZERO_Q = Quat(0, 0, 0, 0)


def assert_quat_zero(name: str, q: Quat) -> None:
    diffs = [sp.simplify(component) for component in q.tuple()]
    if any(diff != 0 for diff in diffs):
        raise AssertionError(f"{name} failed: {diffs}")
    print(f"  {name}: OK")


def quaternion_curvature(d_mu_omega_nu: Quat, d_nu_omega_mu: Quat,
                         omega_mu: Quat, omega_nu: Quat) -> Quat:
    return d_mu_omega_nu - d_nu_omega_mu + omega_mu * omega_nu - omega_nu * omega_mu


def commutator(A: sp.Matrix, B: sp.Matrix) -> sp.Matrix:
    return A * B - B * A


def spin_curvature(d_mu_omega_nu: sp.Matrix, d_nu_omega_mu: sp.Matrix,
                   omega_mu: sp.Matrix, omega_nu: sp.Matrix) -> sp.Matrix:
    return d_mu_omega_nu - d_nu_omega_mu + commutator(omega_mu, omega_nu)


def riemann_curvature(d_mu_gamma_nu_sigma: sp.Expr, d_nu_gamma_mu_sigma: sp.Expr,
                      gamma_mu_lambda: list[sp.Expr], gamma_nu_sigma: list[sp.Expr],
                      gamma_nu_lambda: list[sp.Expr], gamma_mu_sigma: list[sp.Expr]) -> sp.Expr:
    return (
        d_mu_gamma_nu_sigma
        - d_nu_gamma_mu_sigma
        + sum(gamma_mu_lambda[i] * gamma_nu_sigma[i] for i in range(4))
        - sum(gamma_nu_lambda[i] * gamma_mu_sigma[i] for i in range(4))
    )


def main() -> int:
    print("=" * 72)
    print("SECTION 9: CURVATURE -- EXACT SYMPY CHECK")
    print("=" * 72)

    print("\n9.1 Lorentz generators")
    sigma0 = sp.eye(2)
    sigma1 = sp.Matrix([[0, 1], [1, 0]])
    sigma2 = sp.Matrix([[0, -sp.I], [sp.I, 0]])
    sigma3 = sp.Matrix([[1, 0], [0, -1]])
    sigma = [sigma0, sigma1, sigma2, sigma3]
    sigma_ab = {
        (a, b): sp.I / 2 * commutator(sigma[a], sigma[b])
        for a in range(4)
        for b in range(4)
    }
    for a in range(4):
        for b in range(4):
            assert_zero(f"tr sigma_{a}{b} = 0", sp.trace(sigma_ab[(a, b)]))

    print("\n9.1 Quaternion curvature")
    q_symbols = sp.symbols("q0:16")
    q = [Quat(*q_symbols[i:i + 4]) for i in range(0, 16, 4)]
    omega_mn = quaternion_curvature(q[0], q[1], q[2], q[3])
    omega_nm = quaternion_curvature(q[1], q[0], q[3], q[2])
    assert_quat_zero("Omega_nu_mu = -Omega_mu_nu", omega_nm + omega_mn)
    assert_quat_zero("Omega flat = 0", quaternion_curvature(ZERO_Q, ZERO_Q, ZERO_Q, ZERO_Q))

    print("\n9.2 Spin curvature")
    a = sp.symbols("a0:4")
    b = sp.symbols("b0:4")
    c = sp.symbols("c0:4")
    e = sp.symbols("e0:4")
    d_mu = sp.Matrix(2, 2, a)
    d_nu = sp.Matrix(2, 2, b)
    omega_mu = sp.Matrix(2, 2, c)
    omega_nu = sp.Matrix(2, 2, e)
    f_mn = spin_curvature(d_mu, d_nu, omega_mu, omega_nu)
    f_nm = spin_curvature(d_nu, d_mu, omega_nu, omega_mu)
    assert_matrix_zero("F_nu_mu = -F_mu_nu", f_nm + f_mn)
    assert_zero("tr[omega_mu, omega_nu] = 0", sp.trace(commutator(omega_mu, omega_nu)))
    assert_matrix_zero("F flat = 0", spin_curvature(sp.zeros(2), sp.zeros(2), sp.zeros(2), sp.zeros(2)))

    print("\n9.3 Riemann curvature")
    r = sp.symbols("r0:18")
    gml = list(r[2:6])
    gns = list(r[6:10])
    gnl = list(r[10:14])
    gms = list(r[14:18])
    R_mn = riemann_curvature(r[0], r[1], gml, gns, gnl, gms)
    R_nm = riemann_curvature(r[1], r[0], gnl, gms, gml, gns)
    assert_zero("R_nu_mu = -R_mu_nu", R_nm + R_mn)
    assert_zero("R flat = 0", riemann_curvature(0, 0, [0] * 4, [0] * 4, [0] * 4, [0] * 4))

    print("\n9.4/9.5 Curvature bridge zero chain")
    F_zero = sp.zeros(2)
    omega_from_spin_zero = sp.I / 4 * sum((s * F_zero * s for s in sigma), sp.zeros(2))
    assert_matrix_zero("Omega(F=0) = 0", omega_from_spin_zero)

    R_zero = [[0 for _ in range(4)] for _ in range(4)]
    spin_from_riemann_zero = sp.Rational(1, 2) * sum(
        (R_zero[a][b] * sigma_ab[(a, b)] for a in range(4) for b in range(4)),
        sp.zeros(2),
    )
    assert_matrix_zero("F(R=0) = 0", spin_from_riemann_zero)

    print("\nSECTION 9 VERIFIED")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
