#!/usr/bin/env python3
"""SymPy witness for reversible soldering:

    vectors <-> quaternion coordinates <-> 2x2 matrices.

The same four real coordinates can be read as:

* a 4-vector `(t,x,y,z)`;
* a quaternion-like coordinate tuple `t + x i + y j + z k`;
* a real split Pauli matrix `[[t+z, x+y], [x-y, t-z]]`.

The witness checks that the maps are algebraic inverses.
"""

from dataclasses import dataclass

import sympy as sp


def assert_zero(name: str, expr: sp.Expr) -> None:
    simplified = sp.simplify(expr)
    assert simplified == 0, f"{name} failed: {simplified}"
    print(f"OK  {name}")


def assert_matrix_zero(name: str, mat: sp.Matrix) -> None:
    simplified = mat.applyfunc(sp.simplify)
    assert simplified == sp.zeros(*mat.shape), f"{name} failed:\n{simplified}"
    print(f"OK  {name}")


@dataclass(frozen=True)
class Vec4:
    t: sp.Expr
    x: sp.Expr
    y: sp.Expr
    z: sp.Expr


@dataclass(frozen=True)
class Quat4:
    scalar: sp.Expr
    i: sp.Expr
    j: sp.Expr
    k: sp.Expr


def vec_to_quat(v: Vec4) -> Quat4:
    return Quat4(v.t, v.x, v.y, v.z)


def quat_to_vec(q: Quat4) -> Vec4:
    return Vec4(q.scalar, q.i, q.j, q.k)


def vec_to_matrix(v: Vec4) -> sp.Matrix:
    return sp.Matrix([[v.t + v.z, v.x + v.y], [v.x - v.y, v.t - v.z]])


def matrix_to_vec(M: sp.Matrix) -> Vec4:
    return Vec4(
        (M[0, 0] + M[1, 1]) / 2,
        (M[0, 1] + M[1, 0]) / 2,
        (M[0, 1] - M[1, 0]) / 2,
        (M[0, 0] - M[1, 1]) / 2,
    )


def quat_to_matrix(q: Quat4) -> sp.Matrix:
    return vec_to_matrix(quat_to_vec(q))


def matrix_to_quat(M: sp.Matrix) -> Quat4:
    return vec_to_quat(matrix_to_vec(M))


t, x, y, z = sp.symbols("t x y z", real=True)
a, b, c, d = sp.symbols("a b c d", real=True)

v = Vec4(t, x, y, z)
q = Quat4(t, x, y, z)
M = sp.Matrix([[a, b], [c, d]])

round_vec_quat = quat_to_vec(vec_to_quat(v))
assert_zero("Vec -> Quat -> Vec: t", round_vec_quat.t - v.t)
assert_zero("Vec -> Quat -> Vec: x", round_vec_quat.x - v.x)
assert_zero("Vec -> Quat -> Vec: y", round_vec_quat.y - v.y)
assert_zero("Vec -> Quat -> Vec: z", round_vec_quat.z - v.z)

round_quat_vec = vec_to_quat(quat_to_vec(q))
assert_zero("Quat -> Vec -> Quat: scalar", round_quat_vec.scalar - q.scalar)
assert_zero("Quat -> Vec -> Quat: i", round_quat_vec.i - q.i)
assert_zero("Quat -> Vec -> Quat: j", round_quat_vec.j - q.j)
assert_zero("Quat -> Vec -> Quat: k", round_quat_vec.k - q.k)

assert_matrix_zero("Vec -> Matrix -> Vec -> Matrix", vec_to_matrix(matrix_to_vec(vec_to_matrix(v))) - vec_to_matrix(v))
round_v = matrix_to_vec(vec_to_matrix(v))
assert_zero("Vec -> Matrix -> Vec: t", round_v.t - v.t)
assert_zero("Vec -> Matrix -> Vec: x", round_v.x - v.x)
assert_zero("Vec -> Matrix -> Vec: y", round_v.y - v.y)
assert_zero("Vec -> Matrix -> Vec: z", round_v.z - v.z)

assert_matrix_zero("Matrix -> Vec -> Matrix", vec_to_matrix(matrix_to_vec(M)) - M)
assert_matrix_zero("Quat -> Matrix -> Quat -> Matrix", quat_to_matrix(matrix_to_quat(quat_to_matrix(q))) - quat_to_matrix(q))

det_form = sp.factor(vec_to_matrix(v).det())
assert_zero("roundtrip determinant form", det_form - (t**2 - x**2 + y**2 - z**2))

print("OK  reversible soldering Vec4 <-> Quat4 <-> Matrix2 completed")
