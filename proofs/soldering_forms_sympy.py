#!/usr/bin/env python3
"""SymPy witness for Pauli/Cartan soldering forms.

The soldering map sends a real 4-vector `(t,x,y,z)` to the Hermitian Pauli
matrix

    X = t I + x sigma_x + y sigma_y + z sigma_z
      = [[t+z, x-i y], [x+i y, t-z]].

The determinant recovers the Minkowski quadratic form:

    det X = t^2 - x^2 - y^2 - z^2.

This is the algebraic bridge from internal spinor/quaternion data to external
observable spacetime vectors.
"""

import sympy as sp


def assert_zero(name: str, expr: sp.Expr) -> None:
    simplified = sp.simplify(expr)
    assert simplified == 0, f"{name} failed: {simplified}"
    print(f"OK  {name}")


def assert_matrix_zero(name: str, mat: sp.Matrix) -> None:
    simplified = mat.applyfunc(sp.simplify)
    assert simplified == sp.zeros(*mat.shape), f"{name} failed:\n{simplified}"
    print(f"OK  {name}")


t, x, y, z, s, a, b = sp.symbols("t x y z s a b", real=True)
I = sp.I

I2 = sp.eye(2)
sigma_x = sp.Matrix([[0, 1], [1, 0]])
sigma_y = sp.Matrix([[0, -I], [I, 0]])
sigma_z = sp.Matrix([[1, 0], [0, -1]])

X = t * I2 + x * sigma_x + y * sigma_y + z * sigma_z
expected = sp.Matrix([[t + z, x - I * y], [x + I * y, t - z]])
assert_matrix_zero("Pauli soldering matrix expansion", X - expected)

minkowski = t**2 - x**2 - y**2 - z**2
assert_zero("det soldered vector = Minkowski norm", X.det() - minkowski)

assert_matrix_zero("sigma_x square", sigma_x * sigma_x - I2)
assert_matrix_zero("sigma_y square", sigma_y * sigma_y - I2)
assert_matrix_zero("sigma_z square", sigma_z * sigma_z - I2)
assert_matrix_zero("sigma_x anticommutes sigma_y", sigma_x * sigma_y + sigma_y * sigma_x)
assert_matrix_zero("sigma_y anticommutes sigma_z", sigma_y * sigma_z + sigma_z * sigma_y)
assert_matrix_zero("sigma_z anticommutes sigma_x", sigma_z * sigma_x + sigma_x * sigma_z)

scaled_X = (s * t) * I2 + (s * x) * sigma_x + (s * y) * sigma_y + (s * z) * sigma_z
assert_matrix_zero("soldering is linear under Weyl scale", scaled_X - s * X)
assert_zero("det scales quadratically under Weyl scale", scaled_X.det() - s**2 * X.det())

# A rank-one spinor dyad gives a null vector on the conformal boundary.
spinor = sp.Matrix([[a], [b]])
null_X = spinor * spinor.T
assert_zero("spinor dyad boundary vector is null", null_X.det())

print("OK  Pauli soldering form maps spinors/quaternions to 4-vector geometry")
