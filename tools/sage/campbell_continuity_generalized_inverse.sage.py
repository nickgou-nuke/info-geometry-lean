#!/usr/bin/env sage -python
"""Sage exact-rational audit for Campbell 1977 continuity decompositions."""

from sage.all import Matrix, QQ, identity_matrix


def assert_zero_matrix(m, label: str) -> None:
    if not m.is_zero():
        raise AssertionError(f"{label} failed:\n{m}")


def one_norm(m):
    if m.nrows() == 0 or m.ncols() == 0:
        return QQ(0)
    return max(sum(abs(m[i, j]) for i in range(m.nrows())) for j in range(m.ncols()))


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


def moore_penrose_audit() -> None:
    a = Matrix(QQ, [[1, 2, 3], [2, 4, 6]])
    ap = decell_inverse(a)
    f = Matrix(QQ, [[QQ(1) / 100, 0], [-QQ(1) / 150, QQ(1) / 90], [0, QQ(1) / 120]])
    x = ap + f
    im = identity_matrix(QQ, a.nrows())
    inn = identity_matrix(QQ, a.ncols())
    e1 = a * x * a - a
    e2 = x * a * x - x
    e3 = a * x - x.transpose() * a.transpose()
    e4 = x * a - a.transpose() * x.transpose()
    rhs = (
        ap * e1 * ap
        + (inn - ap * a) * e4 * ap
        + ap * e3 * (im - a * ap)
        + (inn - ap * a) * (-e2 + e4 * ap * e3) * (im - a * ap)
    )
    assert_zero_matrix(f - rhs, "Moore-Penrose residual decomposition")
    bound = (
        one_norm(e1) * one_norm(ap) ** 2
        + one_norm(e2) * one_norm(ap * a) * one_norm(im - a * ap)
        + one_norm(e4) * one_norm(inn - ap * a) * one_norm(ap)
        + (one_norm(e2) + one_norm(e4) * one_norm(ap) * one_norm(e3))
        * one_norm(inn - ap * a)
        * one_norm(im - a * ap)
    )
    assert one_norm(f) <= bound
    print("PASS: Moore-Penrose residual decomposition and 1-norm bound")


def group_inverse_audit() -> None:
    a = Matrix(QQ, [[1, 0], [0, 0]])
    ag = a
    f = Matrix(QQ, [[QQ(1) / 50, QQ(1) / 80], [-QQ(1) / 70, QQ(1) / 60]])
    x = ag + f
    ident = identity_matrix(QQ, 2)
    p = ag * a
    e1 = x * a * x - x
    e2 = x * a - a * x
    e3 = a**2 * x - a
    rhs = (
        ag * ag * e3 * p
        + -ag * e2 * (ident - p)
        + (ident - p) * e2 * ag
        + (ident - p) * (-e2 * ag * e2 - e1) * (ident - p)
    )
    assert_zero_matrix(f - rhs, "group-inverse residual decomposition")
    bound = (
        one_norm(ag) ** 2 * one_norm(e3)
        + one_norm(ag) * one_norm(e2) * one_norm(ident - p)
        + one_norm(ident - p) * one_norm(e2) * one_norm(ag)
        + (one_norm(e1) + one_norm(e2) ** 2 * one_norm(ag)) * one_norm(ident - p) ** 2
    )
    assert one_norm(f) <= bound
    print("PASS: group-inverse residual decomposition and 1-norm bound")


def main() -> None:
    moore_penrose_audit()
    group_inverse_audit()
    print("CAMPBELL1977_SAGE_AUDIT_OK")


if __name__ == "__main__":
    main()
