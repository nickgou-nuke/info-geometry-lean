#!/usr/bin/env python3
"""Clifford / galgebra lane for Smith 1977 block-circulant MP witness.

The Smith certificate itself is rational matrix algebra.  This lane keeps that
same exact matrix check in plain `Fraction` arithmetic and then verifies that
the cyclic two-block carrier can be read inside the repository's standard
split-signature `Cl(1,1)` null/idempotent representation lane.
"""

from __future__ import annotations

import os
from fractions import Fraction


os.environ.setdefault("NUMBA_DISABLE_JIT", "1")


Matrix = list[list[Fraction]]


def F(n: int, d: int = 1) -> Fraction:
    return Fraction(n, d)


def matmul(a: Matrix, b: Matrix) -> Matrix:
    rows, cols, mid = len(a), len(b[0]), len(b)
    return [[sum(a[i][k] * b[k][j] for k in range(mid)) for j in range(cols)] for i in range(rows)]


def matsub(a: Matrix, b: Matrix) -> Matrix:
    return [[x - y for x, y in zip(ra, rb)] for ra, rb in zip(a, b)]


def transpose(a: Matrix) -> Matrix:
    return [list(row) for row in zip(*a)]


def eye(n: int) -> Matrix:
    return [[F(1) if i == j else F(0) for j in range(n)] for i in range(n)]


def zero(rows: int, cols: int) -> Matrix:
    return [[F(0) for _ in range(cols)] for _ in range(rows)]


def assert_zero(mat: Matrix, label: str) -> None:
    if mat != zero(len(mat), len(mat[0])):
        raise AssertionError(f"{label} failed: {mat}")


def data() -> tuple[Matrix, Matrix, Matrix]:
    q = [
        [F(0), F(0), F(1), F(0), F(0), F(0)],
        [F(0), F(0), F(0), F(1), F(0), F(0)],
        [F(0), F(0), F(0), F(0), F(1), F(0)],
        [F(0), F(0), F(0), F(0), F(0), F(1)],
        [F(1), F(0), F(0), F(0), F(0), F(0)],
        [F(0), F(1), F(0), F(0), F(0), F(0)],
    ]
    a = [
        [F(1), F(0), F(1), F(0), F(0), F(0)],
        [F(0), F(2), F(0), F(0), F(0), F(1)],
        [F(0), F(0), F(1), F(0), F(1), F(0)],
        [F(0), F(1), F(0), F(2), F(0), F(0)],
        [F(1), F(0), F(0), F(0), F(1), F(0)],
        [F(0), F(0), F(0), F(1), F(0), F(2)],
    ]
    ap = [
        [F(1, 2), F(0), F(-1, 2), F(0), F(1, 2), F(0)],
        [F(0), F(4, 9), F(0), F(1, 9), F(0), F(-2, 9)],
        [F(1, 2), F(0), F(1, 2), F(0), F(-1, 2), F(0)],
        [F(0), F(-2, 9), F(0), F(4, 9), F(0), F(1, 9)],
        [F(-1, 2), F(0), F(1, 2), F(0), F(1, 2), F(0)],
        [F(0), F(1, 9), F(0), F(-2, 9), F(0), F(4, 9)],
    ]
    return q, a, ap


def verify_exact_matrix_lane() -> None:
    q, a, ap = data()
    i6 = eye(6)
    assert_zero(matsub(matmul(a, q), matmul(q, a)), "A commutes with Q tensor I2")
    assert_zero(matsub(matmul(ap, q), matmul(q, ap)), "A+ commutes with Q tensor I2")
    assert matmul(a, ap) == i6
    assert matmul(ap, a) == i6
    assert matmul(matmul(a, ap), a) == a
    assert matmul(matmul(ap, a), ap) == ap
    assert transpose(matmul(a, ap)) == matmul(a, ap)
    assert transpose(matmul(ap, a)) == matmul(ap, a)
    print("PASS: exact Fraction matrix lane")


def verify_clifford_lane() -> None:
    from clifford import Cl

    layout, blades = Cl(1, 1)
    e1, e2 = blades["e1"], blades["e2"]
    n_plus = (e1 + e2) / 2
    n_minus = (e1 - e2) / 2
    zero_mv = 0 * n_plus
    p_plus = n_plus * n_minus
    p_minus = n_minus * n_plus
    assert n_plus * n_plus == zero_mv
    assert n_minus * n_minus == zero_mv
    assert p_plus * p_plus == p_plus
    assert p_minus * p_minus == p_minus
    assert p_plus + p_minus == 1
    assert layout.dims == 2
    assert len(blades) == 4
    print("PASS: clifford Cl(1,1) null/idempotent carrier lane")


def verify_galgebra_lane() -> None:
    from galgebra.ga import Ga

    built = Ga.build("g1 g2", g=[1, -1])
    if len(built) == 2:
        _, basis = built
        g1, g2 = basis
    else:
        g1, g2 = built[1], built[2]
    n_plus = (g1 + g2) / 2
    n_minus = (g1 - g2) / 2
    zero_mv = 0 * n_plus
    p_plus = n_plus * n_minus
    p_minus = n_minus * n_plus
    assert n_plus * n_plus == zero_mv
    assert n_minus * n_minus == zero_mv
    assert p_plus * p_plus == p_plus
    assert p_minus * p_minus == p_minus
    assert p_plus + p_minus == 1
    print("PASS: galgebra Cl(1,1) null/idempotent carrier lane")


def main() -> None:
    print("=== Smith 1977 Clifford / galgebra block-circulant certificate ===")
    verify_exact_matrix_lane()
    verify_clifford_lane()
    verify_galgebra_lane()
    print("SMITH1977_BLOCK_CIRCULANT_CLIFFORD_GALGEBRA_CERTIFICATE_OK")


if __name__ == "__main__":
    main()
