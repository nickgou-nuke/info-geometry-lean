#!/usr/bin/env python3
"""Exact-rational SymPy certificate for Klein-compatible wallpaper symmetries."""

import sympy as sp

T = sp.Matrix([[0, -1], [1, 0]])
G = sp.Matrix([[1, 0], [0, -1]])
I = sp.eye(2)
Z = sp.zeros(2)
D4 = [I, T, -I, -T, G, T*G, -G, -T*G]
eta55 = sp.diag(1, 1, 1, 1, 1, -1, -1, -1, -1, -1)


def main():
    assert eta55.T == eta55
    assert eta55 * eta55 == sp.eye(10)
    assert T*T == -I
    assert G*G == I
    assert G*T == -T*G
    for S in D4:
        assert S.T * S == I
        assert S*T == T*S or S*T == -T*S
        assert S*(T*T) == -S
    assert len({tuple(S) for S in D4}) == 8
    rotations = D4[:4]
    reflections = D4[4:]
    assert all(S*T == T*S for S in rotations)
    assert all(S*T == -T*S for S in reflections)
    # Closure: D4 is closed under multiplication.
    d4set = {tuple(S) for S in D4}
    for A in D4:
        for B in D4:
            assert tuple(A*B) in d4set
    print("wallpaper Klein-bottle Cartan SymPy certificate: ok")


if __name__ == "__main__":
    main()
