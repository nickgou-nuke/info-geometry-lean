#!/usr/bin/env sage -python
"""Sage exact-rational audit for Decell's Cayley-Hamilton generalized inverse."""

from sage.all import Matrix, QQ


def assert_zero_matrix(m, label: str) -> None:
    if not m.is_zero():
        raise AssertionError(f"{label} failed:\n{m}")


def decell_inverse(a):
    b = a * a.transpose()
    coeffs = list(b.charpoly())
    coeffs.reverse()
    k = max(i for i, coeff in enumerate(coeffs) if coeff != 0)
    if k == 0:
        return Matrix(QQ, a.ncols(), a.nrows(), 0)

    tail = Matrix(QQ, b.nrows(), b.ncols(), 0)
    for j in range(k):
        tail += coeffs[j] * (b ** (k - 1 - j))
    return (-QQ(1) / coeffs[k]) * a.transpose() * tail


def check_penrose(a, ap, label: str) -> None:
    assert_zero_matrix(a * ap * a - a, f"{label}: A A+ A = A")
    assert_zero_matrix(ap * a * ap - ap, f"{label}: A+ A A+ = A+")
    assert_zero_matrix((a * ap).transpose() - a * ap, f"{label}: A A+ symmetric")
    assert_zero_matrix((ap * a).transpose() - ap * a, f"{label}: A+ A symmetric")


def run_case(a, label: str) -> None:
    ap = decell_inverse(a)
    check_penrose(a, ap, label)
    print(f"PASS: {label}")
    print(f"  A = {a.list()}")
    print(f"  A+ = {ap.list()}")


def main() -> None:
    run_case(Matrix(QQ, [[1, 2, 3], [2, 4, 6]]), "rank-one rectangular 2x3")
    run_case(Matrix(QQ, [[1, 2], [3, 5]]), "invertible square 2x2")
    run_case(Matrix(QQ, [[1, 0, 1], [0, 1, 1], [1, 1, 2]]), "rank-two symmetric 3x3")
    run_case(Matrix(QQ, 2, 3, 0), "zero rectangular 2x3")
    print("DECELL_CAYLEY_HAMILTON_SAGE_CERTIFICATE_OK")


if __name__ == "__main__":
    main()
