#!/usr/bin/env python3
"""
Finite multi-system verifier for the boundary 5-grading / chiral / tripotent
shadow discussed in the Hestenes-Krein O(5,5) corridor.

This is deliberately a finite algebraic certificate, not a proof of the full
analytic/geometric bulk theory.  It verifies:
  * SymPy: chiral involution, lightcone projectors, tripotent +/-/0 grading,
    and a concrete five-graded matrix-unit bracket shadow.
  * clifford: Cl(5,5) null directions and nilpotent same-arrow boundary bivector.
  * galgebra: symbolic split-signature basis sanity checks.
  * GAP: Weyl group W(D5) order = 1920, the finite Weyl shadow of O(5,5).
  * SageMath: D5 root-system / Lie-algebra dimensions, and W(D5) cardinality.

Honest scope boundary:
  This script does not prove Pin(5,5), holography, analytic continuation,
  Fibonacci anyon universality, or bulk reconstruction.  It verifies the finite
  algebraic shadow mirrored by the Lean file
  lean/InfoGeometry/OperatorAlgebra/BoundaryFiveGradingShadow.lean.
"""

from __future__ import annotations

import os
import subprocess
import tempfile
from pathlib import Path

import sympy as sp

ROOT = Path(__file__).resolve().parents[2]
GAP = Path("/home/goutev/miniforge3/envs/sage/bin/gap")
SAGE = Path("/home/goutev/miniforge3/envs/sage/bin/sage")


def assert_zero_matrix(M: sp.Matrix, name: str) -> None:
    assert M == sp.zeros(*M.shape), f"{name} not zero:\n{M}"


def matrix_unit(n: int, i: int, j: int) -> sp.Matrix:
    M = sp.zeros(n)
    M[i, j] = 1
    return M


def bracket(A: sp.Matrix, B: sp.Matrix) -> sp.Matrix:
    return A * B - B * A


def verify_sympy() -> None:
    I2 = sp.eye(2)
    eps = sp.diag(1, -1)
    boost = sp.Matrix([[0, 1], [1, 0]])
    K = boost * eps
    Pplus = (I2 + eps) / 2
    Pminus = (I2 - eps) / 2

    assert eps * eps == I2
    assert boost * boost == I2
    assert boost * eps == -eps * boost
    assert K * K == -I2
    assert Pplus * Pplus == Pplus
    assert Pminus * Pminus == Pminus
    assert Pplus + Pminus == I2
    assert_zero_matrix(Pplus * Pminus, "Pplus Pminus")
    assert_zero_matrix(Pminus * Pplus, "Pminus Pplus")
    assert eps == Pplus - Pminus

    T = sp.diag(1, -1, 0)
    P = T * T
    z = sp.Matrix([0, 0, 1])
    assert T**3 == T
    assert P * P == P
    assert T * P == T
    assert P * T == T
    assert T * z == sp.zeros(3, 1)

    # Five-graded matrix-unit shadow with coordinates -2,-1,0,+1,+2.
    E = lambda i, j: matrix_unit(5, i, j)
    neg_one_a = E(0, 1)  # grade -1
    neg_one_b = E(1, 2)  # grade -1
    pos_one_a = E(3, 2)  # grade +1
    pos_one_b = E(4, 3)  # grade +1
    mixed_neg = E(1, 2)  # grade -1
    mixed_pos = E(2, 1)  # grade +1
    pos_two = E(4, 2)    # grade +2
    neg_two = E(0, 2)    # grade -2
    zero_diag = E(2, 2)

    assert bracket(pos_one_b, pos_one_a) == pos_two
    assert bracket(neg_one_a, neg_one_b) == neg_two
    assert bracket(mixed_neg, mixed_pos) == E(1, 1) - E(2, 2)
    assert bracket(zero_diag, pos_two) == -pos_two
    assert bracket(zero_diag, neg_two) == -neg_two
    assert_zero_matrix(bracket(pos_two, pos_two), "[g+2,g+2]")

    eta = sp.diag(1, 1, 1, 1, 1, -1, -1, -1, -1, -1)
    flip_negative_1 = sp.diag(1, 1, 1, 1, 1, -1, 1, 1, 1, 1)
    assert flip_negative_1.T * eta * flip_negative_1 == eta
    e1 = sp.eye(10)[:, 0]
    f1 = sp.eye(10)[:, 5]
    n_plus = e1 + f1
    n_minus = e1 - f1
    assert (n_plus.T * eta * n_plus)[0] == 0
    assert (n_minus.T * eta * n_minus)[0] == 0


def mv_scalar(mv):
    return float(mv(0))


def verify_clifford() -> None:
    import clifford

    layout, blades = clifford.Cl(5, 5)
    e = [blades[f"e{i}"] for i in range(1, 11)]

    pseudoscalar = e[0]
    for ei in e[1:]:
        pseudoscalar = pseudoscalar * ei
    assert abs(mv_scalar(pseudoscalar * pseudoscalar) - 1.0) < 1e-9

    n1p = e[0] + e[5]
    n2p = e[1] + e[6]
    n1m = e[0] - e[5]
    assert abs(mv_scalar(n1p * n1p)) < 1e-9
    assert abs(mv_scalar(n1m * n1m)) < 1e-9

    same_arrow_boundary_bivector = n1p ^ n2p
    assert abs(mv_scalar(same_arrow_boundary_bivector * same_arrow_boundary_bivector)) < 1e-9


def verify_galgebra() -> None:
    from galgebra.ga import Ga

    ga = Ga("e1 e2 e3 e4 e5 e6 e7 e8 e9 e10", g=[1, 1, 1, 1, 1, -1, -1, -1, -1, -1])
    e = list(ga.mv_basis)

    # galgebra expressions are symbolic; verify the displayed scalar laws.
    assert str(e[0] * e[0]) == "1"
    assert str(e[5] * e[5]) == "-1"
    n1p = e[0] + e[5]
    n1m = e[0] - e[5]
    assert str((n1p * n1p).simplify()) == "0"
    assert str((n1m * n1m).simplify()) == "0"


def run_gap() -> None:
    if not GAP.exists():
        raise FileNotFoundError(GAP)
    # GAP in this environment does not expose a one-argument WeylGroup(['D',5])
    # constructor.  Build W(D5) concretely as even signed permutations on
    # {±e1,...,±e5}.  Labels 1..5 are +e_i and 6..10 are -e_i.
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
    assert out == "1920", f"unexpected GAP W(D5) order: stdout={proc.stdout!r}; stderr={proc.stderr}"


def run_sage() -> None:
    if not SAGE.exists():
        raise FileNotFoundError(SAGE)
    sage_code = r'''
R = RootSystem(["D", 5])
W = WeylGroup(["D", 5])
positive_roots = len(list(R.root_poset()))
from sage.algebras.lie_algebras.classical_lie_algebra import LieAlgebraChevalleyBasis
g = LieAlgebraChevalleyBasis(QQ, ["D", 5])
print(W.cardinality())
print(positive_roots)
print(g.dimension())
'''
    with tempfile.NamedTemporaryFile("w", suffix=".sage", delete=False) as f:
        f.write(sage_code)
        path = f.name
    try:
        proc = subprocess.run([str(SAGE), path], text=True, capture_output=True, check=True, timeout=120)
    finally:
        os.unlink(path)
    nums = [line.strip() for line in proc.stdout.splitlines() if line.strip().isdigit()]
    assert nums[-3:] == ["1920", "20", "45"], f"unexpected Sage output: {proc.stdout!r}; stderr={proc.stderr}"


def main() -> None:
    verify_sympy()
    verify_clifford()
    verify_galgebra()
    run_gap()
    run_sage()
    print("OK boundary_five_grading_shadow: SymPy + clifford + galgebra + GAP + Sage verified finite shadow")
    print("scope: finite algebraic certificate only; no bulk reconstruction or analytic closure claimed")


if __name__ == "__main__":
    main()
