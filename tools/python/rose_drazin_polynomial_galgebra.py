#!/usr/bin/env python3
"""Galgebra-lane exact rational audit for Rose 1976."""

from __future__ import annotations

from fractions import Fraction

Matrix = list[list[Fraction]]


def mat(rows: list[list[int | Fraction]]) -> Matrix:
    return [[Fraction(x) for x in row] for row in rows]


def eye(n: int) -> Matrix:
    return [[Fraction(int(i == j)) for j in range(n)] for i in range(n)]


def zero(n: int, m: int) -> Matrix:
    return [[Fraction(0) for _ in range(m)] for _ in range(n)]


def add(a: Matrix, b: Matrix) -> Matrix:
    return [[a[i][j] + b[i][j] for j in range(len(a[0]))] for i in range(len(a))]


def neg(a: Matrix) -> Matrix:
    return [[-x for x in row] for row in a]


def sub(a: Matrix, b: Matrix) -> Matrix:
    return add(a, neg(b))


def smul(k: int | Fraction, a: Matrix) -> Matrix:
    return [[Fraction(k) * x for x in row] for row in a]


def mul(a: Matrix, b: Matrix) -> Matrix:
    return [[sum(a[i][k] * b[k][j] for k in range(len(b))) for j in range(len(b[0]))] for i in range(len(a))]


def mpow(a: Matrix, n: int) -> Matrix:
    r = eye(len(a))
    for _ in range(n):
        r = mul(r, a)
    return r


def block_diag(a: Matrix, b: Matrix) -> Matrix:
    top = [row + [Fraction(0)] * len(b[0]) for row in a]
    bot = [[Fraction(0)] * len(a[0]) + row for row in b]
    return top + bot


def is_zero(a: Matrix) -> bool:
    return all(x == 0 for row in a for x in row)


def rose_matrix_audit() -> None:
    n = mat([[0, 1], [0, 0]])
    c = mat([[0, -1], [1, -5]])
    a = block_diag(n, c)
    i2, i4 = eye(2), eye(4)
    assert is_zero(mpow(n, 2))
    assert is_zero(add(add(mpow(c, 2), smul(5, c)), i2))
    x = mul(mpow(a, 2), add(smul(-24, a), smul(-115, i4)))
    expected = block_diag(zero(2, 2), add(neg(c), smul(-5, i2)))
    assert is_zero(sub(x, expected))
    assert is_zero(sub(mul(a, x), mul(x, a)))
    assert is_zero(sub(mul(mul(x, a), x), x))
    assert is_zero(sub(mul(mpow(a, 3), x), mpow(a, 2)))


def main() -> None:
    from galgebra.ga import Ga

    built = Ga.build("e1 e2", g=[1, -1])
    if len(built) == 2:
        _, basis = built
        e1, e2 = basis
    else:
        e1, e2 = built[1], built[2]
    assert (e1 + e2) * (e1 + e2) == 0
    rose_matrix_audit()
    print("ROSE1976_GALGEBRA_AUDIT_OK")


if __name__ == "__main__":
    main()
