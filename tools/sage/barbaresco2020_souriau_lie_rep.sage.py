#!/usr/bin/env sage -python
"""
Sage exact certificate for Barbaresco 2020 finite Souriau representation data.

Run with a writable Sage cache in sandboxed environments, e.g.

  DOT_SAGE=/tmp/sage-dot-sage /home/goutev/miniforge3/envs/sage/bin/python \
    tools/sage/barbaresco2020_souriau_lie_rep.sage.py
"""

from sage.all import Matrix, PolynomialRing, QQ, RootSystem, WeylGroup


def comm(a, b):
    return a * b - b * a


def main() -> None:
    print("=== Sage Barbaresco 2020 Souriau representation certificate ===")

    A1 = RootSystem(["A", 1])
    assert len(A1.index_set()) == 1
    assert 2 * len(list(A1.root_poset())) == 2
    W = WeylGroup(["A", 1])
    assert W.order() == 2
    print("PASS: A1/sl2 root metadata and Weyl order")

    H = Matrix(QQ, [[1, 0], [0, -1]])
    E = Matrix(QQ, [[0, 1], [0, 0]])
    F = Matrix(QQ, [[0, 0], [1, 0]])
    assert comm(H, E) == 2 * E
    assert comm(H, F) == -2 * F
    assert comm(E, F) == H
    print("PASS: sl2 matrix brackets")

    eta = Matrix(QQ, [[1, 0, 0], [0, -1, 0], [0, 0, -1]])
    J = Matrix(QQ, [[0, 0, 0], [0, 0, -1], [0, 1, 0]])
    Kx = Matrix(QQ, [[0, 1, 0], [1, 0, 0], [0, 0, 0]])
    Ky = Matrix(QQ, [[0, 0, 1], [0, 0, 0], [1, 0, 0]])
    Z3 = Matrix.zero(QQ, 3)
    for name, A in [("J", J), ("Kx", Kx), ("Ky", Ky)]:
        assert A.transpose() * eta + eta * A == Z3, name
    assert comm(J, Kx) == Ky
    assert comm(J, Ky) == -Kx
    assert comm(Kx, Ky) == -J
    print("PASS: so(2,1) Lorentz infinitesimal matrices")

    R = PolynomialRing(QQ, "rho,u,v")
    rho, u, v = R.gens()
    r2 = u**2 + v**2
    hyperboloid = (
        (rho * (1 + r2)) ** 2
        - (2 * rho * u) ** 2
        - (2 * rho * v) ** 2
        - rho**2 * (1 - r2) ** 2
    )
    assert hyperboloid == 0
    print("PASS: Poincare-disk moment-map hyperboloid identity")

    Rse = Matrix(QQ, [[0, -1, 0], [1, 0, 0], [0, 0, 0]])
    P1 = Matrix(QQ, [[0, 0, 1], [0, 0, 0], [0, 0, 0]])
    P2 = Matrix(QQ, [[0, 0, 0], [0, 0, 1], [0, 0, 0]])
    assert comm(Rse, P1) == P2
    assert comm(Rse, P2) == -P1
    assert comm(P1, P2) == Z3
    print("PASS: se(2) matrix brackets")

    P = PolynomialRing(QQ, "c,s,mx,my")
    c, s, mx, my = P.gens()
    rotated_norm = (c * mx - s * my) ** 2 + (s * mx + c * my) ** 2
    assert rotated_norm - (mx**2 + my**2) == (c**2 + s**2 - 1) * (mx**2 + my**2)
    print("PASS: SE(2) coadjoint momentum norm rotation invariant")

    print("BARBARESCO2020_SAGE_CERTIFICATE_OK")


if __name__ == "__main__":
    main()
