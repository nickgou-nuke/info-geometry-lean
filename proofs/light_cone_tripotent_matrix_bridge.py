#!/usr/bin/env python3
"""Audit for the light-cone determinant/tripotent matrix bridge."""

import sympy as sp

E, px, py, pz = sp.symbols("E px py pz")
i = sp.I

P = sp.Matrix([[E + pz, px - i * py], [px + i * py, E - pz]])
q = E**2 - px**2 - py**2 - pz**2

E00 = sp.Matrix([[1, 0], [0, 0]])

u0, u1, v0, v1 = sp.symbols("u0 u1 v0 v1")
rank_one = sp.Matrix([[u0 * v0, u0 * v1], [u1 * v0, u1 * v1]])


def main():
    assert sp.simplify(P.det() - q) == 0
    assert E00.det() == 0
    assert E00**3 == E00
    assert sp.simplify(rank_one.det()) == 0

    print("det Pauli(E,px,py,pz) =", sp.factor(P.det()))
    print("Minkowski/light-cone q =", q)
    print("E00 det:", E00.det(), "E00^3=E00:", E00**3 == E00)
    print("outer product det:", sp.factor(rank_one.det()))
    print("Interpretation: det=0 is the complex light cone; normalized rank-one pieces are tripotent representatives.")
    print("light_cone_tripotent_matrix_bridge.py: finite audit passed")


if __name__ == "__main__":
    main()
