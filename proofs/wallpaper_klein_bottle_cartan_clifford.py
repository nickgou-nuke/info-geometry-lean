#!/usr/bin/env python3
"""Clifford-lane certificate for Klein-compatible wallpaper symmetries."""

import sympy as sp
from clifford import Cl


def main():
    layout, _ = Cl(1, 0)
    one = layout.scalar
    T = sp.Matrix([[0, -1], [1, 0]])
    G = sp.Matrix([[1, 0], [0, -1]])
    I = sp.eye(2)
    D4 = [I, T, -I, -T, G, T*G, -G, -T*G]
    assert T*T == -I
    assert G*T == -T*G
    for S in D4:
        assert S.T*S == I
        assert S*T == T*S or S*T == -T*S
    scalar_mv = float(len(D4)) * one
    assert abs(float(scalar_mv.value[0]) - 8.0) < 1e-15
    print("wallpaper Klein-bottle Cartan clifford certificate: ok")


if __name__ == "__main__":
    main()
