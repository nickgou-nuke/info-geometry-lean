#!/usr/bin/env sage -python
"""
Sage exact finite witnesses for the Penrose / braid / Clifford digest.
"""

from sage.all import Matrix, QQ, SymmetricGroup, polygen


def main() -> None:
    print("=== Sage exact Penrose / Artin braid / Clifford digest ===")

    s3 = SymmetricGroup(3)
    s1 = s3("(1,2)")
    s2 = s3("(2,3)")
    assert s1 * s2 * s1 == s2 * s1 * s2
    assert s1**2 == s3.one()
    assert s2**2 == s3.one()
    print("PASS: S3 Artin quotient relation and involutions")

    s5 = SymmetricGroup(5)
    c5 = s5("(1,2,3,4,5)")
    assert c5**5 == s5.one()
    assert c5 != s5.one()
    print("PASS: 5-cycle has order five")

    e = Matrix(QQ, [[0, 1], [1, 0]])
    f = Matrix(QQ, [[0, 1], [-1, 0]])
    assert e * e == Matrix.identity(QQ, 2)
    assert f * f == -Matrix.identity(QQ, 2)
    assert e * f + f * e == Matrix.zero(QQ, 2)
    print("PASS: Clifford matrix pair")

    x = polygen(QQ, "x")
    K = QQ.extension(x**2 - x - 1, "phi")
    phi = K.gen()
    assert phi**2 == phi + 1
    print("PASS: golden field relation phi^2 = phi + 1")

    print("All Sage digest checks passed.")


if __name__ == "__main__":
    main()
