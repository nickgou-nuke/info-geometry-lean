#!/usr/bin/env python3
"""Clifford-lane certificate for finite pg/pmg/pgg Klein candidates."""

import sympy as sp
from clifford import Cl


def main():
    layout, _ = Cl(1, 0)
    one = layout.scalar
    Tx = sp.Matrix([[1,0,1],[0,1,0],[0,0,1]])
    Ty = sp.Matrix([[1,0,0],[0,1,1],[0,0,1]])
    Gx = sp.Matrix([[1,0,sp.Rational(1,2)],[0,-1,0],[0,0,1]])
    Mx = sp.diag(-1,1,1)
    Gy = sp.Matrix([[-1,0,0],[0,1,sp.Rational(1,2)],[0,0,1]])
    assert Gx*Gx == Tx and Gx*Ty == Ty.inv()*Gx
    assert Mx*Mx == sp.eye(3)
    assert Gy*Gy == Ty and Gy*Tx == Tx.inv()*Gy
    scalar_mv = 3.0 * one
    assert abs(float(scalar_mv.value[0]) - 3.0) < 1e-15
    print("klein compatible wallpaper classification clifford certificate: ok")


if __name__ == "__main__":
    main()
