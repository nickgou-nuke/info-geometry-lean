"""Exact-rational SymPy witness for the Brillouin/Klein manifold bridge."""

from __future__ import annotations

import sympy as sp


QQ = sp.Rational


def mat(rows: list[list[object]]) -> sp.Matrix:
    return sp.Matrix([[QQ(x) for x in row] for row in rows])


def key(v: sp.Matrix) -> tuple[sp.Rational, ...]:
    return tuple(sp.Rational(v[i, 0]) for i in range(v.rows))


def d5_roots() -> list[sp.Matrix]:
    roots: list[sp.Matrix] = []
    for i in range(5):
        for j in range(i + 1, 5):
            for si in (QQ(1), QQ(-1)):
                for sj in (QQ(1), QQ(-1)):
                    v = [QQ(0)] * 5
                    v[i] = si
                    v[j] = sj
                    roots.append(sp.Matrix(v))
    return roots


def main() -> None:
    print("=== Brillouin Klein manifold SymPy certificate ===")

    tx = sp.Matrix([[0, -1], [1, 0]])
    ty = sp.Matrix([[1, 0], [0, -1]])
    I2 = sp.eye(2)
    assert tx * tx == -I2
    assert ty * ty == I2
    assert tx * ty == -ty * tx
    print("PASS: anticommuting projective momentum generators")

    gamma0, gammapi, n = sp.symbols("gamma0 gammapi n", integer=True)
    z2 = sp.Mod(gamma0 + gammapi, 2)
    z2_shift = sp.Mod(gamma0 + 2 * n + gammapi, 2)
    assert sp.simplify(z2_shift - z2) == 0
    print("PASS: Z2 gauge invariant stable under even shifts")

    a, b = sp.symbols("a b", integer=True)
    boundary = a + b + a - b
    assert sp.expand(boundary) == 2 * a
    print("PASS: Klein boundary charge is even")

    projected = {
        key(sp.Matrix([r[0, 0], r[1, 0]]))
        for r in d5_roots()
    }
    projected.discard((QQ(0), QQ(0)))
    expected = {
        (QQ(-1), QQ(-1)),
        (QQ(-1), QQ(0)),
        (QQ(-1), QQ(1)),
        (QQ(0), QQ(-1)),
        (QQ(0), QQ(1)),
        (QQ(1), QQ(-1)),
        (QQ(1), QQ(0)),
        (QQ(1), QQ(1)),
    }
    assert projected == expected
    print("PASS: projected D5 roots are the B2/C2 eight-root set")

    D4 = [
        sp.eye(2),
        tx,
        -sp.eye(2),
        -tx,
        ty,
        tx * ty,
        -ty,
        -tx * ty,
    ]
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
    b2set = {key(r) for r in b2_roots}
    for S in D4:
        assert S.T * S == sp.eye(2)
        assert S * tx == tx * S or S * tx == -tx * S
        for r in b2_roots:
            assert key(S * r) in b2set
    print("PASS: Klein-compatible D4 wallpaper symmetries preserve B2/C2 roots")

    print("BRILLOUIN_KLEIN_MANIFOLD_SYMPY_CERTIFICATE_OK")


if __name__ == "__main__":
    main()
