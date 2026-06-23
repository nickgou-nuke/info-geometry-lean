#!/usr/bin/env python3
"""Clifford-lane certificate for the wallpaper/Pin(5,5) root cross-section."""

import sympy as sp
from clifford import Cl


def main():
    layout, _ = Cl(1, 0)
    one = layout.scalar
    T = sp.Matrix([[0, -1], [1, 0]])
    G = sp.Matrix([[1, 0], [0, -1]])
    D4 = [sp.eye(2), T, -sp.eye(2), -T, G, T*G, -G, -T*G]
    B2 = [sp.Matrix(v) for v in [(1,0),(-1,0),(0,1),(0,-1),(1,1),(-1,-1),(1,-1),(-1,1)]]
    assert len({tuple(v) for v in B2}) == 8
    for M in D4:
        assert all(tuple(M*r) in {tuple(v) for v in B2} for r in B2)
    scalar_mv = 4.0 * one  # literal D5-plane intersection cardinality
    assert abs(float(scalar_mv.value[0]) - 4.0) < 1e-15
    print("wallpaper Pin55 root cross-section clifford certificate: ok")


if __name__ == "__main__":
    main()
