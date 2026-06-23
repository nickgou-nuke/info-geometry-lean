#!/usr/bin/env sage -python
"""
Sage exact certificate for Hartwig 1976 Souriau--Frame/Drazin algebra.

Run with:

  DOT_SAGE=/tmp/sage-dot-sage /home/goutev/miniforge3/envs/sage/bin/python \
    tools/sage/hartwig1976_souriau_frame_drazin.sage.py
"""

from sage.all import Matrix, QQ, identity_matrix, polygen


def assert_zero_matrix(m, label: str) -> None:
    if not m.is_zero():
        raise AssertionError(f"{label} failed:\n{m}")


def main() -> None:
    print("=== Hartwig 1976 Souriau--Frame / Drazin Sage certificate ===")

    lam = polygen(QQ, "lambda")
    a = Matrix(QQ, [[0, 0, 0], [0, 2, 0], [0, 0, 3]])
    ident = identity_matrix(QQ, 3)
    char_poly = (lam * ident - a).det().factor()
    assert char_poly == (lam * (lam - 2) * (lam - 3)).factor()
    print("PASS: characteristic polynomial has one zero root")

    a0 = Matrix(QQ, [[6, 0, 0], [0, 0, 0], [0, 0, 0]])
    a1 = Matrix(QQ, [[-5, 0, 0], [0, -3, 0], [0, 0, -2]])
    x = (ident - QQ(1) / QQ(6) * a0) * (-QQ(1) / QQ(6) * a1)
    expected = Matrix(QQ, [[0, 0, 0], [0, QQ(1) / QQ(2), 0], [0, 0, QQ(1) / QQ(3)]])
    assert x == expected
    print("PASS: Hartwig coefficient formula gives A#")

    assert_zero_matrix(a * x * a - a, "A X A = A")
    assert_zero_matrix(x * a * x - x, "X A X = X")
    assert_zero_matrix(a * x - x * a, "A X = X A")
    assert_zero_matrix(a**2 * x - a, "A^2 X = A")
    print("PASS: group inverse / Drazin index-one laws")

    z = ident - a * x
    assert z == Matrix(QQ, [[1, 0, 0], [0, 0, 0], [0, 0, 0]])
    assert_zero_matrix(z**2 - z, "Z^2 = Z")
    assert_zero_matrix(a * z, "A Z = 0")
    assert_zero_matrix(z * a, "Z A = 0")
    print("PASS: principal idempotent is the zero-root projector")

    p = Matrix(QQ, [[0, 1, 0], [1, 0, 0], [0, 0, 1]])
    ac = p * a * p.inverse()
    xc = p * x * p.inverse()
    assert_zero_matrix(ac * xc * ac - ac, "conjugated A X A = A")
    assert_zero_matrix(xc * ac * xc - xc, "conjugated X A X = X")
    assert_zero_matrix(ac * xc - xc * ac, "conjugated commutation")
    print("PASS: GL_3 conjugation preserves the representation")

    print("HARTWIG1976_SAGE_CERTIFICATE_OK")


if __name__ == "__main__":
    main()
