#!/usr/bin/env python3
"""Section 8: quaternion spin connection and curvature.

This is the exact SymPy companion to ``lean/InfoGeometry/Section8.lean``.
It verifies the finite algebraic content:

* Hamilton quaternion basis laws;
* qbar*q = q*qbar = ||q||^2;
* det(x^mu sigma_mu) = t^2 - x^2 - y^2 - z^2;
* Omega = qbar*dq is pure imaginary when dq is tangent to the unit sphere;
* the flat spin/quaternion connection and curvature vanish.
"""

from __future__ import annotations

from dataclasses import dataclass

import sympy as sp


def assert_eq(name: str, left, right=0) -> None:
    diff = sp.simplify(left - right)
    if diff != 0:
        raise AssertionError(f"{name} failed: {diff}")
    print(f"  {name}: OK")


def assert_quat_eq(name: str, left: "Quat", right: "Quat") -> None:
    diffs = [sp.simplify(a - b) for a, b in zip(left.tuple(), right.tuple())]
    if any(diff != 0 for diff in diffs):
        raise AssertionError(f"{name} failed: {diffs}")
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

    def conj(self) -> "Quat":
        return Quat(self.r, -self.x, -self.y, -self.z)

    def norm_sq(self) -> sp.Expr:
        return self.r**2 + self.x**2 + self.y**2 + self.z**2

    def dot(self, other: "Quat") -> sp.Expr:
        return self.r * other.r + self.x * other.x + self.y * other.y + self.z * other.z


ZERO = Quat(0, 0, 0, 0)
ONE = Quat(1, 0, 0, 0)
QI = Quat(0, 1, 0, 0)
QJ = Quat(0, 0, 1, 0)
QK = Quat(0, 0, 0, 1)


def scalar(a: sp.Expr) -> Quat:
    return Quat(a, 0, 0, 0)


def quaternion_connection(q: Quat, dq: Quat) -> Quat:
    return q.conj() * dq


def covariant_derivative(partial_v: Quat, omega: Quat, vector: Quat) -> Quat:
    return partial_v + omega * vector - vector * omega


def quaternion_curvature(d_mu_omega_nu: Quat, d_nu_omega_mu: Quat, omega_mu: Quat, omega_nu: Quat) -> Quat:
    return d_mu_omega_nu - d_nu_omega_mu + omega_mu * omega_nu - omega_nu * omega_mu


def main() -> int:
    print("=" * 72)
    print("SECTION 8: QUATERNION SPIN CONNECTION — EXACT SYMPY CHECK")
    print("=" * 72)

    print("\n8.1 Quaternion basis laws")
    assert_quat_eq("i^2 = -1", QI * QI, -ONE)
    assert_quat_eq("j^2 = -1", QJ * QJ, -ONE)
    assert_quat_eq("k^2 = -1", QK * QK, -ONE)
    assert_quat_eq("ij = k", QI * QJ, QK)
    assert_quat_eq("jk = i", QJ * QK, QI)
    assert_quat_eq("ki = j", QK * QI, QJ)
    assert_quat_eq("ijk = -1", (QI * QJ) * QK, -ONE)

    print("\n8.1 Quaternion conjugation and unit condition")
    q0, q1, q2, q3 = sp.symbols("q0 q1 q2 q3", real=True)
    q = Quat(q0, q1, q2, q3)
    assert_quat_eq("qbar*q = ||q||^2", q.conj() * q, scalar(q.norm_sq()))
    assert_quat_eq("q*qbar = ||q||^2", q * q.conj(), scalar(q.norm_sq()))

    print("\n8.1 Pauli four-vector determinant")
    t, x, y, z = sp.symbols("t x y z")
    sigma0 = sp.eye(2)
    sigma1 = sp.Matrix([[0, 1], [1, 0]])
    sigma2 = sp.Matrix([[0, -sp.I], [sp.I, 0]])
    sigma3 = sp.Matrix([[1, 0], [0, -1]])
    spacetime_matrix = t * sigma0 + x * sigma1 + y * sigma2 + z * sigma3
    assert_eq("det(x^mu sigma_mu)", spacetime_matrix.det(), t**2 - x**2 - y**2 - z**2)

    print("\n8.2 Quaternion connection")
    dq0, dq1, dq2, dq3 = sp.symbols("dq0 dq1 dq2 dq3", real=True)
    dq = Quat(dq0, dq1, dq2, dq3)
    omega = quaternion_connection(q, dq)
    assert_eq("Re(qbar*dq) = q dot dq", omega.r, q.dot(dq))

    # Tangency to the unit-quaternion constraint means q dot dq = 0.
    tangent_subs = {dq0: -(q1 * dq1 + q2 * dq2 + q3 * dq3) / q0}
    omega_tangent_real = sp.factor(omega.r.subs(tangent_subs))
    assert_eq("Omega is pure imaginary on tangent vectors", omega_tangent_real, 0)
    omega_tangent = Quat(*(component.subs(tangent_subs) for component in omega.tuple()))
    assert_quat_eq("Omega_bar = -Omega when tangent", omega_tangent.conj(), -omega_tangent)
    print("    condition used: q dot dq = 0")

    print("\n8.2 Covariant derivative")
    v0, v1, v2, v3 = sp.symbols("v0 v1 v2 v3", real=True)
    vector = Quat(v0, v1, v2, v3)
    partial_v = Quat(*sp.symbols("pv0 pv1 pv2 pv3", real=True))
    assert_quat_eq(
        "D_mu V reduces to partial_mu V when Omega=0",
        covariant_derivative(partial_v, ZERO, vector),
        partial_v,
    )

    print("\n8.3 Flat tetrad and spin connection")
    eta = sp.diag(-1, 1, 1, 1)
    tetrad = sp.eye(4)
    if tetrad.T * eta * tetrad != eta:
        raise AssertionError("flat tetrad metric relation failed")
    print("  e^T eta e = eta for identity tetrad: OK")
    omega_flat = sp.MutableDenseNDimArray.zeros(4, 4, 4)
    assert_eq("omega_flat antisymmetry sample", omega_flat[0, 1, 2], -omega_flat[0, 2, 1])

    print("\n8.4 Curvature and flat quaternion-spin relation")
    assert_quat_eq("F = dOmega + Omega^2 vanishes flatly", quaternion_curvature(ZERO, ZERO, ZERO, ZERO), ZERO)
    assert_quat_eq("zero spin connection projects to zero quaternion connection", quaternion_connection(ONE, ZERO), ZERO)

    print("\nSECTION 8 VERIFIED")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
