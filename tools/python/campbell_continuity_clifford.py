#!/usr/bin/env python3
"""Clifford-lane exact rational audit for Campbell 1977."""

from __future__ import annotations

from fractions import Fraction

Matrix = list[list[Fraction]]


def mat(rows: list[list[int | Fraction]]) -> Matrix:
    return [[Fraction(x) for x in row] for row in rows]


def eye(n: int) -> Matrix:
    return [[Fraction(int(i == j)) for j in range(n)] for i in range(n)]


def transpose(a: Matrix) -> Matrix:
    return [list(row) for row in zip(*a)]


def add(a: Matrix, b: Matrix) -> Matrix:
    return [[a[i][j] + b[i][j] for j in range(len(a[0]))] for i in range(len(a))]


def neg(a: Matrix) -> Matrix:
    return [[-x for x in row] for row in a]


def sub(a: Matrix, b: Matrix) -> Matrix:
    return add(a, neg(b))


def mul(a: Matrix, b: Matrix) -> Matrix:
    return [[sum(a[i][k] * b[k][j] for k in range(len(b))) for j in range(len(b[0]))] for i in range(len(a))]


def norm1(a: Matrix) -> Fraction:
    return max(sum(abs(a[i][j]) for i in range(len(a))) for j in range(len(a[0])))


def zero(a: Matrix) -> bool:
    return all(x == 0 for row in a for x in row)


def mp_audit() -> None:
    A = mat([[1, 2, 3], [2, 4, 6]])
    Ap = mat([[Fraction(1, 70), Fraction(1, 35)], [Fraction(1, 35), Fraction(2, 35)], [Fraction(3, 70), Fraction(3, 35)]])
    F = mat([[Fraction(1, 100), 0], [Fraction(-1, 150), Fraction(1, 90)], [0, Fraction(1, 120)]])
    X = add(Ap, F)
    Im, In = eye(2), eye(3)
    E1 = sub(mul(mul(A, X), A), A)
    E2 = sub(mul(mul(X, A), X), X)
    E3 = sub(mul(A, X), mul(transpose(X), transpose(A)))
    E4 = sub(mul(X, A), mul(transpose(A), transpose(X)))
    rhs = add(add(mul(mul(Ap, E1), Ap), mul(mul(sub(In, mul(Ap, A)), E4), Ap)),
              add(mul(mul(Ap, E3), sub(Im, mul(A, Ap))),
                  mul(mul(sub(In, mul(Ap, A)), add(neg(E2), mul(mul(E4, Ap), E3))), sub(Im, mul(A, Ap)))))
    assert zero(sub(F, rhs))
    bound = norm1(E1) * norm1(Ap) ** 2 + norm1(E2) * norm1(mul(Ap, A)) * norm1(sub(Im, mul(A, Ap)))
    assert norm1(F) <= bound + norm1(E4) * norm1(sub(In, mul(Ap, A))) * norm1(Ap) + (norm1(E2) + norm1(E4) * norm1(Ap) * norm1(E3)) * norm1(sub(In, mul(Ap, A))) * norm1(sub(Im, mul(A, Ap)))


def group_audit() -> None:
    A = mat([[1, 0], [0, 0]])
    Ag = A
    F = mat([[Fraction(1, 50), Fraction(1, 80)], [Fraction(-1, 70), Fraction(1, 60)]])
    X = add(Ag, F)
    I = eye(2)
    P = mul(Ag, A)
    E1 = sub(mul(mul(X, A), X), X)
    E2 = sub(mul(X, A), mul(A, X))
    E3 = sub(mul(mul(A, A), X), A)
    rhs = add(add(mul(mul(mul(Ag, Ag), E3), P), neg(mul(mul(Ag, E2), sub(I, P)))),
              add(mul(mul(sub(I, P), E2), Ag),
                  mul(mul(sub(I, P), sub(neg(mul(mul(E2, Ag), E2)), E1)), sub(I, P))))
    assert zero(sub(F, rhs))
    bound = norm1(Ag) ** 2 * norm1(E3) + norm1(Ag) * norm1(E2) * norm1(sub(I, P))
    assert norm1(F) <= bound + norm1(sub(I, P)) * norm1(E2) * norm1(Ag) + (norm1(E1) + norm1(E2) ** 2 * norm1(Ag)) * norm1(sub(I, P)) ** 2


def main() -> None:
    from clifford import Cl

    _, blades = Cl(1, 1)
    e1, e2 = blades["e1"], blades["e2"]
    n = e1 + e2
    assert n * n == 0
    mp_audit()
    group_audit()
    print("CAMPBELL1977_CLIFFORD_AUDIT_OK")


if __name__ == "__main__":
    main()
