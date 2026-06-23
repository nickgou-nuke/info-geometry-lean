#!/usr/bin/env python3
"""Galgebra-lane exact rational audit for Campbell 1977."""

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
    a = mat([[1, 2, 3], [2, 4, 6]])
    ap = mat([[Fraction(1, 70), Fraction(1, 35)], [Fraction(1, 35), Fraction(2, 35)], [Fraction(3, 70), Fraction(3, 35)]])
    f = mat([[Fraction(1, 100), 0], [Fraction(-1, 150), Fraction(1, 90)], [0, Fraction(1, 120)]])
    x = add(ap, f)
    im, inn = eye(2), eye(3)
    e1 = sub(mul(mul(a, x), a), a)
    e2 = sub(mul(mul(x, a), x), x)
    e3 = sub(mul(a, x), mul(transpose(x), transpose(a)))
    e4 = sub(mul(x, a), mul(transpose(a), transpose(x)))
    rhs = add(add(mul(mul(ap, e1), ap), mul(mul(sub(inn, mul(ap, a)), e4), ap)),
              add(mul(mul(ap, e3), sub(im, mul(a, ap))),
                  mul(mul(sub(inn, mul(ap, a)), add(neg(e2), mul(mul(e4, ap), e3))), sub(im, mul(a, ap)))))
    assert zero(sub(f, rhs))
    bound = norm1(e1) * norm1(ap) ** 2 + norm1(e2) * norm1(mul(ap, a)) * norm1(sub(im, mul(a, ap)))
    assert norm1(f) <= bound + norm1(e4) * norm1(sub(inn, mul(ap, a))) * norm1(ap) + (norm1(e2) + norm1(e4) * norm1(ap) * norm1(e3)) * norm1(sub(inn, mul(ap, a))) * norm1(sub(im, mul(a, ap)))


def group_audit() -> None:
    a = mat([[1, 0], [0, 0]])
    ag = a
    f = mat([[Fraction(1, 50), Fraction(1, 80)], [Fraction(-1, 70), Fraction(1, 60)]])
    x = add(ag, f)
    ident = eye(2)
    p = mul(ag, a)
    e1 = sub(mul(mul(x, a), x), x)
    e2 = sub(mul(x, a), mul(a, x))
    e3 = sub(mul(mul(a, a), x), a)
    rhs = add(add(mul(mul(mul(ag, ag), e3), p), neg(mul(mul(ag, e2), sub(ident, p)))),
              add(mul(mul(sub(ident, p), e2), ag),
                  mul(mul(sub(ident, p), sub(neg(mul(mul(e2, ag), e2)), e1)), sub(ident, p))))
    assert zero(sub(f, rhs))
    bound = norm1(ag) ** 2 * norm1(e3) + norm1(ag) * norm1(e2) * norm1(sub(ident, p))
    assert norm1(f) <= bound + norm1(sub(ident, p)) * norm1(e2) * norm1(ag) + (norm1(e1) + norm1(e2) ** 2 * norm1(ag)) * norm1(sub(ident, p)) ** 2


def main() -> None:
    from galgebra.ga import Ga

    built = Ga.build("e1 e2", g=[1, -1])
    if len(built) == 2:
        _, basis = built
        e1, e2 = basis
    else:
        e1, e2 = built[1], built[2]
    n = e1 + e2
    assert n * n == 0
    mp_audit()
    group_audit()
    print("CAMPBELL1977_GALGEBRA_AUDIT_OK")


if __name__ == "__main__":
    main()
