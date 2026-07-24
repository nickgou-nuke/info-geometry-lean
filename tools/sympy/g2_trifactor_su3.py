#!/usr/bin/env python3
"""Finite Zorn projector checks for G2TrifactorSU3.lean.

This script mirrors the closed finite corridor in
lean/InfoGeometry/Algebra/Zorn/G2TrifactorSU3.lean:

MATHEMATICAL CONTEXT:
  - G₂ is the automorphism group of split octonions, with Lie algebra dimension 14.
  - A chosen-direction stabilizer has dimension 8.
  - Its real form is not determined by dimension alone.

CHECKS:
* OP1 and OP2 are idempotent and cubic projectors for the canonical Zorn
  vector-matrix product.
* OP1 * X * OP2 isolates the upper-right three-vector.
* OP2 * X * OP1 isolates the lower-left three-vector.

It does not claim or test an identification of a stabilizer with compact SU(3)
or a full G₂ classification. Dimension data from external calculations are
not used as proof authority.
"""

from __future__ import annotations

from dataclasses import dataclass

import sympy as sp


Vector3 = tuple[sp.Expr, sp.Expr, sp.Expr]
Quaternion4 = tuple[sp.Expr, sp.Expr, sp.Expr, sp.Expr]


@dataclass(frozen=True)
class Zorn:
    a: sp.Expr
    b: sp.Expr
    x: Vector3
    y: Vector3


def dot(u: Vector3, v: Vector3) -> sp.Expr:
    return sp.expand(sum(ui * vi for ui, vi in zip(u, v)))


def cross(u: Vector3, v: Vector3) -> Vector3:
    return (
        sp.expand(u[1] * v[2] - u[2] * v[1]),
        sp.expand(u[2] * v[0] - u[0] * v[2]),
        sp.expand(u[0] * v[1] - u[1] * v[0]),
    )


def vadd(u: Vector3, v: Vector3) -> Vector3:
    return tuple(sp.expand(ui + vi) for ui, vi in zip(u, v))  # type: ignore[return-value]


def vsub(u: Vector3, v: Vector3) -> Vector3:
    return tuple(sp.expand(ui - vi) for ui, vi in zip(u, v))  # type: ignore[return-value]


def smul(c: sp.Expr, u: Vector3) -> Vector3:
    return tuple(sp.expand(c * ui) for ui in u)  # type: ignore[return-value]


def zmul(left: Zorn, right: Zorn) -> Zorn:
    return Zorn(
        a=sp.expand(left.a * right.a + dot(left.x, right.y)),
        b=sp.expand(left.b * right.b + dot(left.y, right.x)),
        x=vsub(vadd(smul(left.a, right.x), smul(right.b, left.x)), cross(left.y, right.y)),
        y=vadd(vadd(smul(left.b, right.y), smul(right.a, left.y)), cross(left.x, right.x)),
    )


def assert_zorn_equal(actual: Zorn, expected: Zorn) -> None:
    fields = [
        sp.expand(actual.a - expected.a),
        sp.expand(actual.b - expected.b),
        *(sp.expand(a - e) for a, e in zip(actual.x, expected.x)),
        *(sp.expand(a - e) for a, e in zip(actual.y, expected.y)),
    ]
    assert all(field == 0 for field in fields), (actual, expected, fields)


@dataclass(frozen=True)
class Bektas:
    q1: Quaternion4
    q2: Quaternion4


def qmul(p: Quaternion4, q: Quaternion4) -> Quaternion4:
    a, b, c, d = p
    e, f, g, h = q
    return (
        sp.expand(a * e - b * f - c * g - d * h),
        sp.expand(a * f + b * e + c * h - d * g),
        sp.expand(a * g - b * h + c * e + d * f),
        sp.expand(a * h + b * g - c * f + d * e),
    )


def qnorm(q: Quaternion4) -> sp.Expr:
    return sp.expand(sum(component**2 for component in q))


def assert_quaternion_equal(actual: Quaternion4, expected: Quaternion4) -> None:
    fields = [sp.expand(a - e) for a, e in zip(actual, expected)]
    assert all(field == 0 for field in fields), (actual, expected, fields)


def assert_bektas_equal(actual: Bektas, expected: Bektas) -> None:
    assert_quaternion_equal(actual.q1, expected.q1)
    assert_quaternion_equal(actual.q2, expected.q2)


def color_act(u: Quaternion4, state: Bektas) -> Bektas:
    return Bektas(q1=state.q1, q2=qmul(u, state.q2))


def split_norm(state: Bektas) -> sp.Expr:
    return sp.expand(qnorm(state.q1) - qnorm(state.q2))


def main() -> None:
    a, b = sp.symbols("a b")
    x1, x2, x3 = sp.symbols("x1 x2 x3")
    y1, y2, y3 = sp.symbols("y1 y2 y3")

    zero: Vector3 = (sp.Integer(0), sp.Integer(0), sp.Integer(0))
    op1 = Zorn(sp.Integer(1), sp.Integer(0), zero, zero)
    op2 = Zorn(sp.Integer(0), sp.Integer(1), zero, zero)
    x = (x1, x2, x3)
    y = (y1, y2, y3)
    cell = Zorn(a, b, x, y)

    assert_zorn_equal(zmul(op1, op1), op1)
    assert_zorn_equal(zmul(op2, op2), op2)
    assert_zorn_equal(zmul(zmul(op1, op1), op1), op1)
    assert_zorn_equal(zmul(zmul(op2, op2), op2), op2)

    assert_zorn_equal(zmul(zmul(op1, cell), op2), Zorn(0, 0, x, zero))
    assert_zorn_equal(zmul(zmul(op2, cell), op1), Zorn(0, 0, zero, y))

    u0, u1, u2, u3 = sp.symbols("u0 u1 u2 u3")
    v0, v1, v2, v3 = sp.symbols("v0 v1 v2 v3")
    p0, p1, p2, p3 = sp.symbols("p0 p1 p2 p3")
    r0, r1, r2, r3 = sp.symbols("r0 r1 r2 r3")

    one_q: Quaternion4 = (sp.Integer(1), sp.Integer(0), sp.Integer(0), sp.Integer(0))
    u: Quaternion4 = (u0, u1, u2, u3)
    v: Quaternion4 = (v0, v1, v2, v3)
    state = Bektas(q1=(p0, p1, p2, p3), q2=(r0, r1, r2, r3))

    assert_bektas_equal(color_act(one_q, state), state)
    assert_bektas_equal(color_act(qmul(u, v), state), color_act(u, color_act(v, state)))

    norm_mul_residual = sp.expand(qnorm(qmul(u, state.q2)) - qnorm(u) * qnorm(state.q2))
    assert norm_mul_residual == 0
    split_norm_residual = sp.expand(
        split_norm(color_act(u, state)) - (qnorm(state.q1) - qnorm(u) * qnorm(state.q2))
    )
    assert split_norm_residual == 0

    print("G2TrifactorSU3 finite Zorn projector checks passed.")


if __name__ == "__main__":
    main()
