#!/usr/bin/env sage -python
"""
Sage exact certificate for Greville 1973 Souriau--Frame/Drazin algebra.

Run with:

  DOT_SAGE=/tmp/sage-dot-sage /home/goutev/miniforge3/envs/sage/bin/python \
    tools/sage/greville1973_souriau_frame_drazin.sage.py
"""

from sage.all import Matrix, QQ, identity_matrix


def assert_zero_matrix(m, label: str) -> None:
    if not m.is_zero():
        raise AssertionError(f"{label} failed:\n{m}")


def main() -> None:
    print("=== Greville 1973 Souriau--Frame / Drazin Sage certificate ===")

    a = Matrix(QQ, [[0, 1, 0], [0, 0, 0], [0, 0, 2]])
    ident = identity_matrix(QQ, 3)

    b0 = ident
    p1 = (a * b0).trace()
    b1 = a * b0 - p1 * ident
    p2 = QQ(1) / QQ(2) * (a * b1).trace()
    b2 = a * b1 - p2 * ident
    p3 = QQ(1) / QQ(3) * (a * b2).trace()
    b3 = a * b2 - p3 * ident

    assert p1 == 2
    assert p2 == 0
    assert p3 == 0
    assert not b2.is_zero()
    assert b3.is_zero()
    print("PASS: Souriau--Frame recurrence has r=3, s=1, k=2")

    k = 2
    x = p1 ** (-(k + 1)) * (a**k) * (b0 ** (k + 1))
    expected = Matrix(QQ, [[0, 0, 0], [0, 0, 0], [0, 0, QQ(1) / QQ(2)]])
    assert x == expected
    print("PASS: Greville formula gives the expected Drazin inverse")

    assert_zero_matrix(a * x - x * a, "A X = X A")
    assert_zero_matrix(x * a * x - x, "X A X = X")
    assert_zero_matrix(a ** (k + 1) * x - a**k, "A^(k+1) X = A^k")
    assert_zero_matrix(a * x * x - x, "A X^2 = X")
    print("PASS: Drazin index-2 equations hold")

    regular = a * x
    nilpotent = ident - regular
    assert regular == Matrix(QQ, [[0, 0, 0], [0, 0, 0], [0, 0, 1]])
    assert nilpotent == Matrix(QQ, [[1, 0, 0], [0, 1, 0], [0, 0, 0]])
    assert_zero_matrix(regular**2 - regular, "regular projector")
    assert_zero_matrix(nilpotent**2 - nilpotent, "nilpotent projector")
    assert_zero_matrix((a * nilpotent) ** 2, "nilpotent lane square-zero")
    print("PASS: Drazin projectors split regular and nilpotent lanes")

    p = Matrix(QQ, [[0, 0, 1], [0, 1, 0], [1, 0, 0]])
    ac = p * a * p.inverse()
    xc = p * x * p.inverse()
    assert_zero_matrix(ac * xc - xc * ac, "conjugated commutation")
    assert_zero_matrix(xc * ac * xc - xc, "conjugated X A X = X")
    assert_zero_matrix(ac ** (k + 1) * xc - ac**k, "conjugated Drazin power law")
    print("PASS: GL_3(Q) conjugation preserves the Drazin packet")

    print("GREVILLE1973_SAGE_CERTIFICATE_OK")


if __name__ == "__main__":
    main()
