#!/usr/bin/env python3
"""Galgebra-lane exact rational audit for Decell 1965.

Run with the Sage Python environment when plain Python lacks `galgebra`:

  /home/goutev/miniforge3/envs/sage/bin/python \
    tools/python/decell_cayley_hamilton_galgebra.py
"""

from __future__ import annotations

from fractions import Fraction


Matrix = list[list[Fraction]]


def mat(rows: list[list[int | Fraction]]) -> Matrix:
    return [[Fraction(x) for x in row] for row in rows]


def transpose(a: Matrix) -> Matrix:
    return [list(row) for row in zip(*a)]


def mmul(a: Matrix, b: Matrix) -> Matrix:
    return [
        [sum(a[i][k] * b[k][j] for k in range(len(b))) for j in range(len(b[0]))]
        for i in range(len(a))
    ]


def msub(a: Matrix, b: Matrix) -> Matrix:
    return [[a[i][j] - b[i][j] for j in range(len(a[0]))] for i in range(len(a))]


def is_zero(a: Matrix) -> bool:
    return all(x == 0 for row in a for x in row)


def check_penrose(a: Matrix, ap: Matrix, label: str) -> None:
    if not is_zero(msub(mmul(mmul(a, ap), a), a)):
        raise AssertionError(f"{label}: A A+ A = A failed")
    if not is_zero(msub(mmul(mmul(ap, a), ap), ap)):
        raise AssertionError(f"{label}: A+ A A+ = A+ failed")
    aap = mmul(a, ap)
    if not is_zero(msub(transpose(aap), aap)):
        raise AssertionError(f"{label}: A A+ symmetric failed")
    apa = mmul(ap, a)
    if not is_zero(msub(transpose(apa), apa)):
        raise AssertionError(f"{label}: A+ A symmetric failed")
    print(f"PASS: {label}")


def main() -> None:
    from galgebra.ga import Ga

    built = Ga.build("e1 e2", g=[1, -1])
    if len(built) == 2:
        _, basis = built
        e1, e2 = basis
    else:
        e1, e2 = built[1], built[2]
    n = e1 + e2
    assert (e1 * e1).scalar() == 1
    assert (e2 * e2).scalar() == -1
    assert e1 * e2 + e2 * e1 == 0
    assert n * n == 0
    print("PASS: galgebra Cl(1,1) null direction squares to zero")

    check_penrose(
        mat([[1, 2, 3], [2, 4, 6]]),
        mat([[Fraction(1, 70), Fraction(1, 35)], [Fraction(1, 35), Fraction(2, 35)], [Fraction(3, 70), Fraction(3, 35)]]),
        "rank-one rectangular 2x3",
    )
    check_penrose(mat([[1, 2], [3, 5]]), mat([[-5, 2], [3, -1]]), "invertible square 2x2")
    check_penrose(
        mat([[1, 0, 1], [0, 1, 1], [1, 1, 2]]),
        mat([[Fraction(5, 9), Fraction(-4, 9), Fraction(1, 9)], [Fraction(-4, 9), Fraction(5, 9), Fraction(1, 9)], [Fraction(1, 9), Fraction(1, 9), Fraction(2, 9)]]),
        "rank-two symmetric 3x3",
    )
    check_penrose(mat([[0, 0, 0], [0, 0, 0]]), mat([[0, 0], [0, 0], [0, 0]]), "zero rectangular 2x3")
    print("DECELL_CAYLEY_HAMILTON_GALGEBRA_CERTIFICATE_OK")


if __name__ == "__main__":
    main()
