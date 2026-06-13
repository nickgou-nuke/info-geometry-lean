#!/usr/bin/env python3
"""Finite merged Bogoliubov/Pauli soldered-frame checks.

This script mirrors `InfoGeometry.Physics.BogoliubovPauliSolderedFrame`.
The canonical merged finite Bogoljubov frame has one mode carrying both
coordinates:

* the operator coordinate uses a phase-linear/phase-antilinear split
  represented here by symbolic matrices `L` and `C`;
* the Pauli/tetrad coordinate uses soldering as the visible matrix leg.
"""

from __future__ import annotations

import sympy as sp


t, z, x, y = sp.symbols("t z x y", real=True)

sigma0 = sp.Matrix([[1, 0], [0, 1]])
sigma1 = sp.Matrix([[0, 1], [1, 0]])
sigma3 = sp.Matrix([[1, 0], [0, -1]])
epsilon = sp.Matrix([[0, 1], [-1, 0]])


def soldering(tt: sp.Expr, zz: sp.Expr, xx: sp.Expr, yy: sp.Expr) -> sp.Matrix:
    return tt * sigma0 + zz * sigma3 + xx * sigma1 + yy * epsilon


def bogoliubov_annihilator(tt: sp.Expr, zz: sp.Expr, xx: sp.Expr, yy: sp.Expr) -> sp.Matrix:
    return soldering(tt, zz, xx, yy)


def bogoliubov_creator(_tt: sp.Expr, _zz: sp.Expr, _xx: sp.Expr, _yy: sp.Expr) -> sp.Matrix:
    return sp.zeros(2)


def single_bogoljubov_pauli_tetrad_annihilator(
    linear: sp.Matrix,
    tt: sp.Expr,
    zz: sp.Expr,
    xx: sp.Expr,
    yy: sp.Expr,
) -> tuple[sp.Matrix, sp.Matrix]:
    return linear, soldering(tt, zz, xx, yy)


def single_bogoljubov_pauli_tetrad_creator(
    antilinear: sp.Matrix,
) -> tuple[sp.Matrix, sp.Matrix]:
    return antilinear, sp.zeros(2)


def unified_operator_mode(linear: sp.Matrix, antilinear: sp.Matrix) -> tuple[sp.Matrix, sp.Matrix]:
    return linear, sp.zeros(2)


def unified_operator_creator(_linear: sp.Matrix, antilinear: sp.Matrix) -> tuple[sp.Matrix, sp.Matrix]:
    return antilinear, sp.zeros(2)


def unified_pauli_mode(tt: sp.Expr, zz: sp.Expr, xx: sp.Expr, yy: sp.Expr) -> tuple[sp.Matrix, sp.Matrix]:
    return sp.zeros(2), soldering(tt, zz, xx, yy)


def unified_pauli_creator(_tt: sp.Expr, _zz: sp.Expr, _xx: sp.Expr, _yy: sp.Expr) -> tuple[sp.Matrix, sp.Matrix]:
    return sp.zeros(2), sp.zeros(2)


def assert_zero(name: str, value: sp.Matrix | sp.Expr) -> None:
    simplified = value.applyfunc(sp.simplify) if isinstance(value, sp.MatrixBase) else sp.simplify(value)
    if simplified != (sp.zeros(*value.shape) if isinstance(value, sp.MatrixBase) else 0):
        raise AssertionError(f"{name} failed: {simplified}")


frame_readout = bogoliubov_annihilator(t, z, x, y) + bogoliubov_creator(t, z, x, y)
assert_zero("merged Bogoliubov frame reconstructs Pauli/tetrad soldering", frame_readout - soldering(t, z, x, y))

q22 = t**2 - z**2 - x**2 + y**2
assert_zero("soldered Bogoliubov-frame determinant", sp.det(bogoliubov_annihilator(t, z, x, y)) - q22)

L = sp.Matrix(sp.symbols("l00 l01 l10 l11")).reshape(2, 2)
C = sp.Matrix(sp.symbols("c00 c01 c10 c11")).reshape(2, 2)
A = L + C
op_ann = unified_operator_mode(L, C)
op_cre = unified_operator_creator(L, C)
assert_zero("unified operator adapter first component", op_ann[0] + op_cre[0] - A)
assert_zero("unified operator adapter second component", op_ann[1] + op_cre[1])

pauli_ann = unified_pauli_mode(t, z, x, y)
pauli_cre = unified_pauli_creator(t, z, x, y)
assert_zero("unified Pauli adapter first component", pauli_ann[0] + pauli_cre[0])
assert_zero("unified Pauli adapter second component", pauli_ann[1] + pauli_cre[1] - soldering(t, z, x, y))

single_ann = single_bogoljubov_pauli_tetrad_annihilator(L, t, z, x, y)
single_cre = single_bogoljubov_pauli_tetrad_creator(C)
assert_zero("single merged Bogoljubov operator component", single_ann[0] + single_cre[0] - A)
assert_zero(
    "single merged Bogoljubov Pauli/tetrad component",
    single_ann[1] + single_cre[1] - soldering(t, z, x, y),
)

print("OK  merged Bogoliubov/Pauli soldered-frame checks")
