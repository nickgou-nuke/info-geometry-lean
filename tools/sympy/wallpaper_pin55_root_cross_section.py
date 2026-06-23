#!/usr/bin/env python3
"""Exact-rational SymPy certificate for the wallpaper/Pin(5,5) root cross-section."""

from __future__ import annotations

import itertools

import sympy as sp


def mat_tuple(M: sp.Matrix) -> tuple:
    return tuple(M)


def vec_tuple(v: sp.Matrix) -> tuple:
    return tuple(v)


def block_diag(A: sp.Matrix, B: sp.Matrix) -> sp.Matrix:
    return sp.diag(A, B)


def main() -> None:
    print("=== Wallpaper / Pin(5,5) root cross-section SymPy certificate ===")

    I2 = sp.eye(2)
    I5 = sp.eye(5)
    T = sp.Matrix([[0, -1], [1, 0]])
    G = sp.diag(1, -1)
    D4 = [I2, T, -I2, -T, G, T * G, -G, -T * G]
    D4set = {mat_tuple(S) for S in D4}

    # All signed-permutation point symmetries of the square wallpaper cell.
    signed_perm_2 = []
    for perm in itertools.permutations(range(2)):
        for signs in itertools.product([1, -1], repeat=2):
            M = sp.zeros(2)
            for col, row in enumerate(perm):
                M[row, col] = signs[col]
            signed_perm_2.append(M)
    compatible = [
        S for S in signed_perm_2
        if S.T * S == I2 and (S * T == T * S or S * T == -T * S)
    ]
    assert {mat_tuple(S) for S in compatible} == D4set
    assert len(D4set) == 8
    for A in D4:
        for B in D4:
            assert mat_tuple(A * B) in D4set
    print("PASS: compatible wallpaper point symmetries are exactly D4")

    b2_roots = [
        sp.Matrix([1, 0]),
        sp.Matrix([-1, 0]),
        sp.Matrix([0, 1]),
        sp.Matrix([0, -1]),
        sp.Matrix([1, 1]),
        sp.Matrix([-1, -1]),
        sp.Matrix([1, -1]),
        sp.Matrix([-1, 1]),
    ]
    b2set = {vec_tuple(r) for r in b2_roots}
    for S in D4:
        for r in b2_roots:
            assert vec_tuple(S * r) in b2set
    print("PASS: D4 preserves the projected B2/C2 root system")

    d5_roots = []
    for i in range(5):
        for j in range(i + 1, 5):
            for si in [1, -1]:
                for sj in [1, -1]:
                    r = sp.zeros(5, 1)
                    r[i, 0] = si
                    r[j, 0] = sj
                    d5_roots.append(r)
                    d5_roots.append(-r)
    d5set = {vec_tuple(r) for r in d5_roots}
    assert len(d5set) == 40
    projected = {vec_tuple(sp.Matrix([r[0, 0], r[1, 0]])) for r in d5_roots}
    assert b2set == {p for p in projected if p != (0, 0)}
    print("PASS: nonzero projection of D5 roots is exactly B2/C2")

    lifts = [
        sp.Matrix([1, 0, 1, 0, 0]),
        sp.Matrix([-1, 0, 1, 0, 0]),
        sp.Matrix([0, 1, 1, 0, 0]),
        sp.Matrix([0, -1, 1, 0, 0]),
        sp.Matrix([1, 1, 0, 0, 0]),
        sp.Matrix([-1, -1, 0, 0, 0]),
        sp.Matrix([1, -1, 0, 0, 0]),
        sp.Matrix([-1, 1, 0, 0, 0]),
    ]
    for lift, root in zip(lifts, b2_roots):
        assert vec_tuple(lift) in d5set
        assert sp.Matrix([lift[0, 0], lift[1, 0]]) == root
    print("PASS: every B2/C2 root has an explicit D5 root lift")

    cross = [
        I5,
        sp.Matrix([[0, -1, 0, 0, 0], [1, 0, 0, 0, 0], [0, 0, -1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 0, 0, 1]]),
        sp.diag(-1, -1, 1, 1, 1),
        sp.Matrix([[0, 1, 0, 0, 0], [-1, 0, 0, 0, 0], [0, 0, -1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 0, 0, 1]]),
        sp.diag(1, -1, -1, 1, 1),
        sp.Matrix([[0, 1, 0, 0, 0], [1, 0, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 0, 0, 1]]),
        sp.diag(-1, 1, -1, 1, 1),
        sp.Matrix([[0, -1, 0, 0, 0], [-1, 0, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 0, 0, 1]]),
    ]
    eta55 = sp.diag(1, 1, 1, 1, 1, -1, -1, -1, -1, -1)
    for P, S in zip(cross, D4):
        assert P.T * P == I5
        assert P[:2, :2] == S
        assert all(vec_tuple(P * r) in d5set for r in d5_roots)
        L = block_diag(P, P)
        assert L.T * eta55 * L == eta55
    print("PASS: D4 cross-section lifts to D5 Weyl signed permutations preserving O(5,5)")

    print("WALLPAPER_PIN55_ROOT_CROSS_SECTION_SYMPY_CERTIFICATE_OK")


if __name__ == "__main__":
    main()
