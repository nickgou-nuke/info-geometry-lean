#!/usr/bin/env python3
"""
SymPy certificate for Barbaresco 2020 finite Souriau representation data.

Checks:
* strict sl2 matrix brackets;
* the equivalent so(2,1) Lorentz infinitesimal representation;
* the Poincare disk moment map hyperboloid identity;
* strict SE(2) homogeneous matrix multiplication and Lie brackets; and
* the finite Gaussian log-partition derivatives used in the SE(2) example.
"""

from __future__ import annotations

import sys
from pathlib import Path
import sympy as sp

_REPO_ROOT = Path(__file__).resolve().parents[2]
if str(_REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(_REPO_ROOT))

from tools.sympy.common import assert_matrix_zero, comm

assert_zero_matrix = assert_matrix_zero


def zmat(n: int) -> sp.Matrix:
    return sp.zeros(n)


def se2_group(c: sp.Expr, s: sp.Expr, tx: sp.Expr, ty: sp.Expr) -> sp.Matrix:
    return sp.Matrix([[c, -s, tx], [s, c, ty], [0, 0, 1]])


def main() -> None:
    print("=== Barbaresco 2020 Souriau algebra / representation certificate ===")

    H = sp.Matrix([[1, 0], [0, -1]])
    E = sp.Matrix([[0, 1], [0, 0]])
    F = sp.Matrix([[0, 0], [1, 0]])
    assert_zero_matrix(comm(H, E) - 2 * E, "sl2 [H,E]=2E")
    assert_zero_matrix(comm(H, F) + 2 * F, "sl2 [H,F]=-2F")
    assert_zero_matrix(comm(E, F) - H, "sl2 [E,F]=H")
    print("PASS: strict sl2 matrix brackets")

    eta = sp.diag(1, -1, -1)
    J = sp.Matrix([[0, 0, 0], [0, 0, -1], [0, 1, 0]])
    Kx = sp.Matrix([[0, 1, 0], [1, 0, 0], [0, 0, 0]])
    Ky = sp.Matrix([[0, 0, 1], [0, 0, 0], [1, 0, 0]])
    for name, A in [("J", J), ("Kx", Kx), ("Ky", Ky)]:
        assert_zero_matrix(A.T * eta + eta * A, f"so(2,1) infinitesimal {name}")
    assert_zero_matrix(comm(J, Kx) - Ky, "so21 [J,Kx]=Ky")
    assert_zero_matrix(comm(J, Ky) + Kx, "so21 [J,Ky]=-Kx")
    assert_zero_matrix(comm(Kx, Ky) + J, "so21 [Kx,Ky]=-J")
    print("PASS: strict so(2,1) Lorentz representation")

    rho, u, v = sp.symbols("rho u v", real=True)
    r2 = u**2 + v**2
    hyperboloid_cleared = sp.expand(
        (rho * (1 + r2)) ** 2 - (2 * rho * u) ** 2 - (2 * rho * v) ** 2
        - rho**2 * (1 - r2) ** 2
    )
    assert sp.simplify(hyperboloid_cleared) == 0
    print("PASS: SU(1,1) disk moment-map hyperboloid identity")

    c1, s1, x1, y1, c2, s2, x2, y2 = sp.symbols(
        "c1 s1 x1 y1 c2 s2 x2 y2", real=True
    )
    lhs = se2_group(c1, s1, x1, y1) * se2_group(c2, s2, x2, y2)
    rhs = se2_group(
        c1 * c2 - s1 * s2,
        s1 * c2 + c1 * s2,
        c1 * x2 - s1 * y2 + x1,
        s1 * x2 + c1 * y2 + y1,
    )
    assert_zero_matrix(lhs - rhs, "SE(2) homogeneous group multiplication")

    Jse = sp.Matrix([[0, -1, 0], [1, 0, 0], [0, 0, 0]])
    P1 = sp.Matrix([[0, 0, 1], [0, 0, 0], [0, 0, 0]])
    P2 = sp.Matrix([[0, 0, 0], [0, 0, 1], [0, 0, 0]])
    assert_zero_matrix(comm(Jse, P1) - P2, "se2 [J,P1]=P2")
    assert_zero_matrix(comm(Jse, P2) + P1, "se2 [J,P2]=-P1")
    assert_zero_matrix(comm(P1, P2), "se2 [P1,P2]=0")
    print("PASS: strict SE(2) group law and Lie brackets")

    c, s, mx, my = sp.symbols("c s mx my", real=True)
    rotated_norm = sp.expand((c * mx - s * my) ** 2 + (s * mx + c * my) ** 2)
    norm_diff = sp.factor(rotated_norm - (mx**2 + my**2))
    assert sp.simplify(norm_diff.subs(c**2 + s**2, 1)) == 0 or norm_diff == (
        c**2 + s**2 - 1
    ) * (mx**2 + my**2)
    print("PASS: SE(2) coadjoint momentum norm rotation invariant")

    b, B1, B2 = sp.symbols("b B1 B2", real=True, nonzero=True)
    phi = sp.log(-2 * sp.pi / b) - (B1**2 + B2**2) / (2 * b)
    assert sp.simplify(sp.diff(phi, b) - (-1 / b + (B1**2 + B2**2) / (2 * b**2))) == 0
    assert sp.simplify(sp.diff(phi, B1) + B1 / b) == 0
    assert sp.simplify(sp.diff(phi, B2) + B2 / b) == 0
    print("PASS: SE(2) Gaussian log-partition derivative identities")

    print("BARBARESCO2020_SYMPY_CERTIFICATE_OK")


if __name__ == "__main__":
    main()
