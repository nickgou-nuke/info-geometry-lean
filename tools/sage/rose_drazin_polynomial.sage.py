#!/usr/bin/env sage -python
"""Sage exact-rational audit for Rose 1976 Drazin polynomial."""

from sage.all import Matrix, QQ, block_diagonal_matrix, identity_matrix


def assert_zero_matrix(m, label: str) -> None:
    if not m.is_zero():
        raise AssertionError(f"{label} failed:\n{m}")


def main() -> None:
    n = Matrix(QQ, [[0, 1], [0, 0]])
    c = Matrix(QQ, [[0, -1], [1, -5]])
    a = block_diagonal_matrix(n, c)
    ident = identity_matrix(QQ, 4)

    assert_zero_matrix(n**2, "nilpotent block N^2 = 0")
    assert_zero_matrix(c**2 + 5 * c + identity_matrix(QQ, 2), "C^2+5C+I=0")

    x = a**2 * (-24 * a - 115 * ident)
    expected = block_diagonal_matrix(Matrix(QQ, 2, 2, 0), -c - 5 * identity_matrix(QQ, 2))
    assert_zero_matrix(x - expected, "Rose polynomial equals block Drazin candidate")

    assert_zero_matrix(a * x - x * a, "A X = X A")
    assert_zero_matrix(x * a * x - x, "X A X = X")
    assert_zero_matrix(a**3 * x - a**2, "A^(k+1) X = A^k")
    print("ROSE1976_SAGE_AUDIT_OK")


if __name__ == "__main__":
    main()
