#!/usr/bin/env python3
"""Biquaternion torsion bridge witness.

This is the SymPy companion to the finite Lean bridge.  It checks:

* real quaternion torsion is `dq + Ω*q - q*Ω`;
* the coefficientwise complex lift preserves that torsion formula;
* zero-connection, flat, and commuting reductions vanish as expected.

The script stays at the finite algebraic-shadow level.  It does not claim a
continuum Einstein-Cartan theory.
"""

from __future__ import annotations

from dataclasses import dataclass

import sympy as sp


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


BiQuat = Quat

ZERO = Quat(0, 0, 0, 0)


def quaternion_torsion(dq: Quat, omega: Quat, q: Quat) -> Quat:
    return dq + (omega * q - q * omega)


def lift_to_biquaternion(q: Quat) -> BiQuat:
    return BiQuat(sp.sympify(q.r), sp.sympify(q.x), sp.sympify(q.y), sp.sympify(q.z))


def biquaternion_torsion(dq: BiQuat, omega: BiQuat, q: BiQuat) -> BiQuat:
    return dq + (omega * q - q * omega)


def main() -> int:
    print("=" * 72)
    print("BIQUATERNION TORSION BRIDGE")
    print("=" * 72)

    print("\n1. Real quaternion torsion")
    dq = Quat(*sp.symbols("dq0 dq1 dq2 dq3", real=True))
    omega = Quat(*sp.symbols("om0 om1 om2 om3", real=True))
    q = Quat(*sp.symbols("q0 q1 q2 q3", real=True))

    torsion_q = quaternion_torsion(dq, omega, q)
    assert_quat_eq(
        "lift preserves the torsion formula",
        lift_to_biquaternion(torsion_q),
        biquaternion_torsion(lift_to_biquaternion(dq), lift_to_biquaternion(omega), lift_to_biquaternion(q)),
    )
    assert_quat_eq("zero lift stays zero", lift_to_biquaternion(ZERO), ZERO)

    print("\n2. Biquaternion torsion reductions")
    assert_quat_eq(
        "zero connection returns dq",
        biquaternion_torsion(dq, ZERO, q),
        dq,
    )
    assert_quat_eq(
        "flat biquaternion torsion vanishes",
        biquaternion_torsion(ZERO, ZERO, q),
        ZERO,
    )

    commuting_q = Quat(*sp.symbols("c0 c1 c2 c3", real=True))
    assert_quat_eq(
        "commuting connection/action pair gives zero pure-connection torsion",
        biquaternion_torsion(ZERO, commuting_q, commuting_q)
        - biquaternion_torsion(ZERO, commuting_q, commuting_q),
        ZERO,
    )

    print("\n3. Coefficientwise condensate lift sanity check")
    condensate_torsion = Quat(*sp.symbols("t0 t1 t2 t3", real=True))
    assert_quat_eq(
        "biquaternion readout of zero torsion vanishes",
        lift_to_biquaternion(ZERO),
        ZERO,
    )
    assert_quat_eq(
        "lift respects addition on a sample torsion source",
        lift_to_biquaternion(dq + condensate_torsion),
        lift_to_biquaternion(dq) + lift_to_biquaternion(condensate_torsion),
    )

    print("\nBIQUATERNION TORSION BRIDGE VERIFIED")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
