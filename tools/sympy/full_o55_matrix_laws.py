#!/usr/bin/env python3
"""Full finite matrix-law verifier for O(5,5) / so(5,5).

This is the assertion-first companion to
  lean/InfoGeometry/OperatorAlgebra/FullO55MatrixLaws.lean

It verifies the complete 45-generator split block basis of so(5,5), canonical
W(D5) signed-permutation O(5,5) generators, null light-cone directions, and the
D5 root count.  It does not claim Pin(5,5), analytic holography, or universal
bulk reconstruction.
"""
from __future__ import annotations

import subprocess
import tempfile
from pathlib import Path
import os

import sympy as sp

GAP = Path("/home/goutev/miniforge3/envs/sage/bin/gap")
SAGE = Path("/home/goutev/miniforge3/envs/sage/bin/sage")

n = 5
N = 10
eta = sp.diag(*([1] * n + [-1] * n))
I10 = sp.eye(N)
Z10 = sp.zeros(N)


def E(i: int, j: int) -> sp.Matrix:
    M = sp.zeros(N)
    M[i, j] = 1
    return M


def is_o55(A: sp.Matrix) -> bool:
    return sp.simplify(A.T * eta * A - eta) == Z10


def is_so55(X: sp.Matrix) -> bool:
    return sp.simplify(X.T * eta + eta * X) == Z10


import sys

_REPO_ROOT = Path(__file__).resolve().parents[2]
if str(_REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(_REPO_ROOT))

from tools.sympy.common import comm


def rot_plus(i: int, j: int) -> sp.Matrix:
    return E(i, j) - E(j, i)


def rot_minus(i: int, j: int) -> sp.Matrix:
    return E(n + i, n + j) - E(n + j, n + i)


def boost(i: int, j: int) -> sp.Matrix:
    return E(i, n + j) + E(n + j, i)


def perm_matrix(p: list[int]) -> sp.Matrix:
    M = sp.zeros(N)
    for col, row in enumerate(p):
        M[row, col] = 1
    return M


def verify_sympy_full_o55() -> None:
    assert eta * eta == I10
    assert sp.trace(eta) == 0

    basis: list[sp.Matrix] = []
    basis += [rot_plus(i, j) for i in range(n) for j in range(i + 1, n)]
    basis += [rot_minus(i, j) for i in range(n) for j in range(i + 1, n)]
    basis += [boost(i, j) for i in range(n) for j in range(n)]
    assert len(basis) == 45
    assert all(is_so55(X) for X in basis)

    # Lie closure for the complete 45 x 45 table: [X,Y] is in so(5,5).
    for X in basis:
        for Y in basis:
            assert is_so55(comm(X, Y))

    cartan = [boost(i, i) for i in range(n)]
    for H in cartan:
        assert is_so55(H)
    for H in cartan:
        for K in cartan:
            assert comm(H, K) == Z10

    # Coordinate-pair permutations and sign flips preserve the split form.
    # These are concrete O(5,5) matrix representatives; the abstract W(D5)
    # order is checked separately in GAP/Sage on the root lattice.
    pair_perms = [
        [1, 0, 2, 3, 4, 6, 5, 7, 8, 9],
        [0, 2, 1, 3, 4, 5, 7, 6, 8, 9],
        [0, 1, 3, 2, 4, 5, 6, 8, 7, 9],
        [0, 1, 2, 4, 3, 5, 6, 7, 9, 8],
    ]
    for p in pair_perms:
        assert is_o55(perm_matrix(p))

    # Sign flips are in O(5,5).  A two-coordinate sign flip is the concrete
    # vector-space shadow of an even signed Weyl reflection; a one-coordinate
    # sign flip witnesses the larger disconnected O(5,5) ambient group.
    even_sign_flip = sp.diag(-1, -1, 1, 1, 1, -1, -1, 1, 1, 1)
    sign_flip = sp.diag(-1, 1, 1, 1, 1, 1, 1, 1, 1, 1)
    assert is_o55(even_sign_flip)
    assert is_o55(sign_flip)

    # Null cone directions e_i +/- f_i are isotropic and paired by O(5,5).
    for i in range(n):
        ep = sp.eye(N)[:, i]
        fm = sp.eye(N)[:, n + i]
        np = ep + fm
        nm = ep - fm
        assert (np.T * eta * np)[0] == 0
        assert (nm.T * eta * nm)[0] == 0
        assert (np.T * eta * nm)[0] == 2


def verify_clifford() -> None:
    import clifford
    layout, blades = clifford.Cl(5, 5)
    e = [blades[f"e{i}"] for i in range(1, 11)]
    ps = e[0]
    for ei in e[1:]:
        ps = ps * ei
    assert abs(float((ps * ps)(0)) - 1.0) < 1e-9
    bivectors = [e[i] ^ e[j] for i in range(N) for j in range(i + 1, N)]
    assert len(bivectors) == 45
    n1 = e[0] + e[5]
    n2 = e[1] + e[6]
    B = n1 ^ n2
    assert abs(float((n1 * n1)(0))) < 1e-9
    assert abs(float((B * B)(0))) < 1e-9


def verify_galgebra() -> None:
    from galgebra.ga import Ga
    ga = Ga("e1 e2 e3 e4 e5 e6 e7 e8 e9 e10", g=[1,1,1,1,1,-1,-1,-1,-1,-1])
    e = list(ga.mv_basis)
    assert str(e[0] * e[0]) == "1"
    assert str(e[5] * e[5]) == "-1"
    assert str(((e[0] + e[5]) * (e[0] + e[5])).simplify()) == "0"


def verify_gap() -> None:
    script = """
s1 := (1,2)(6,7);;
s2 := (2,3)(7,8);;
s3 := (3,4)(8,9);;
s4 := (4,5)(9,10);;
s5 := (4,10)(5,9);;
W := Group([s1,s2,s3,s4,s5]);;
Print(Size(W), "\\n");
quit;
"""
    proc = subprocess.run([str(GAP), "-q"], input=script, text=True, capture_output=True, check=True)
    out = "".join(ch for ch in proc.stdout if ch.isdigit())
    assert out == "1920", (proc.stdout, proc.stderr)


def verify_sage() -> None:
    code = r'''
R = RootSystem(["D", 5])
W = WeylGroup(["D", 5])
from sage.algebras.lie_algebras.classical_lie_algebra import LieAlgebraChevalleyBasis
g = LieAlgebraChevalleyBasis(QQ, ["D", 5])
print(W.cardinality())
print(len(list(R.root_poset())))
print(g.dimension())
'''
    with tempfile.NamedTemporaryFile("w", suffix=".sage", delete=False) as f:
        f.write(code)
        path = f.name
    try:
        proc = subprocess.run([str(SAGE), path], text=True, capture_output=True, check=True, timeout=120)
    finally:
        os.unlink(path)
    nums = [line.strip() for line in proc.stdout.splitlines() if line.strip().isdigit()]
    assert nums[-3:] == ["1920", "20", "45"], (proc.stdout, proc.stderr)


def main() -> None:
    verify_sympy_full_o55()
    verify_clifford()
    verify_galgebra()
    verify_gap()
    verify_sage()
    print("OK full_o55_matrix_laws: complete 45-generator so(5,5), O(5,5) Weyl/sign actions, null cone, Cl(5,5), GAP, Sage verified")
    print("scope: finite matrix-law owner; Pin lift and analytic/holographic reconstruction remain separate closure debt")


if __name__ == "__main__":
    main()
