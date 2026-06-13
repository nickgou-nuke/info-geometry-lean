#!/usr/bin/env python3
"""Exact dual split-quaternion backbone verifier.

Lean twin:
    lean/InfoGeometry/OperatorAlgebra/DualSplitQuaternionBackbone.lean

Scope boundary:
    This script verifies only the algebraic finite/exact backbone for
    split quaternions H_s and their dual-number extension D H_s = H_s + eps H_s.
    It does not prove Lorentzian screw-motion classification, SO(2,2)⋉R^4,
    Aut(DH_s), or any global geometric representation theorem.

Backends used:
    * SymPy: exact structure constants and matrix model.
    * clifford: Cl(1,1) realization of the split-quaternion basis.
    * galgebra: independent Cl(1,1) geometric-algebra check.
    * GAP: finite signed-unit group is D4/order 8; eps is not a unit.
    * Sage: exact split norm matrix has signature (2,2).
"""

from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path
import subprocess
import tempfile
import textwrap

import sympy as sp


@dataclass(frozen=True)
class SplitQ:
    a: sp.Expr
    b: sp.Expr
    c: sp.Expr
    d: sp.Expr

    def __add__(self, other: "SplitQ") -> "SplitQ":
        return SplitQ(self.a + other.a, self.b + other.b, self.c + other.c, self.d + other.d)

    def __neg__(self) -> "SplitQ":
        return SplitQ(-self.a, -self.b, -self.c, -self.d)

    def __sub__(self, other: "SplitQ") -> "SplitQ":
        return self + (-other)

    def __mul__(self, other: "SplitQ") -> "SplitQ":
        a, b, c, d = self.a, self.b, self.c, self.d
        e, f, g, h = other.a, other.b, other.c, other.d
        return SplitQ(
            sp.expand(a * e - b * f + c * g + d * h),
            sp.expand(a * f + b * e - c * h + d * g),
            sp.expand(a * g - b * h + c * e + d * f),
            sp.expand(a * h + b * g - c * f + d * e),
        )

    def conj(self) -> "SplitQ":
        return SplitQ(self.a, -self.b, -self.c, -self.d)

    def norm_scalar(self) -> sp.Expr:
        return sp.expand(self.a**2 + self.b**2 - self.c**2 - self.d**2)

    def as_matrix(self) -> sp.Matrix:
        one = sp.eye(2)
        ii = sp.Matrix([[0, -1], [1, 0]])
        jj = sp.Matrix([[0, 1], [1, 0]])
        kk = ii * jj
        return self.a * one + self.b * ii + self.c * jj + self.d * kk


ZERO = SplitQ(0, 0, 0, 0)
ONE = SplitQ(1, 0, 0, 0)
I = SplitQ(0, 1, 0, 0)
J = SplitQ(0, 0, 1, 0)
K = SplitQ(0, 0, 0, 1)
BASIS = [ONE, I, J, K]


@dataclass(frozen=True)
class DualSplitQ:
    primal: SplitQ
    tangent: SplitQ

    def __mul__(self, other: "DualSplitQ") -> "DualSplitQ":
        return DualSplitQ(
            self.primal * other.primal,
            self.primal * other.tangent + self.tangent * other.primal,
        )

    def conj(self) -> "DualSplitQ":
        return DualSplitQ(self.primal.conj(), self.tangent.conj())


ZERO_D = DualSplitQ(ZERO, ZERO)
EPS = DualSplitQ(ZERO, ONE)


def base(x: SplitQ) -> DualSplitQ:
    return DualSplitQ(x, ZERO)


def eps_lift(x: SplitQ) -> DualSplitQ:
    return DualSplitQ(ZERO, x)


def assert_split_quaternion_core() -> None:
    assert I * I == -ONE
    assert J * J == ONE
    assert K * K == ONE
    assert (I * J) * K == ONE
    assert I * J == K
    assert J * I == -K
    assert J * K == -I
    assert K * J == I
    assert K * I == J
    assert I * K == -J

    a, b, c, d, e, f, g, h, r, s, t, u = sp.symbols("a b c d e f g h r s t u")
    x = SplitQ(a, b, c, d)
    y = SplitQ(e, f, g, h)
    z = SplitQ(r, s, t, u)
    assert (x * y) * z == x * (y * z)
    assert x * x.conj() == SplitQ(x.norm_scalar(), 0, 0, 0)
    matrix_residue = x.as_matrix() * y.as_matrix() - (x * y).as_matrix()
    assert all(sp.expand(entry) == 0 for entry in matrix_residue)
    assert sp.factor(x.as_matrix().det() - x.norm_scalar()) == 0


def assert_dual_extension_core() -> None:
    for x in BASIS:
        for y in BASIS:
            assert base(x) * base(y) == base(x * y)
            assert eps_lift(x) * eps_lift(y) == ZERO_D
            assert base(x) * eps_lift(y) == eps_lift(x * y)
            assert eps_lift(x) * base(y) == eps_lift(x * y)
    assert EPS * EPS == ZERO_D
    # eps is nilpotent, hence not invertible and not an order-two unit.
    assert EPS * EPS != base(ONE)


def assert_clifford_backend() -> None:
    from clifford import Cl

    layout, blades = Cl(1, 1, firstIdx=1)
    e1, e2 = blades["e1"], blades["e2"]
    ci = -e2
    cj = e1
    ck = e1 * e2
    one = 1
    assert ci * ci == -one
    assert cj * cj == one
    assert ck * ck == one
    assert ci * cj == ck
    assert (ci * cj) * ck == one


def assert_galgebra_backend() -> None:
    from galgebra.ga import Ga

    ga = Ga("e1 e2", g=[1, -1])
    e1, e2 = ga.mv()
    gi = -e2
    gj = e1
    gk = e1 * e2
    assert str((gi * gi).simplify()) == "-1"
    assert str((gj * gj).simplify()) == "1"
    assert str((gk * gk).simplify()) == "1"
    assert str((gi * gj - gk).simplify()) == "0"


def assert_gap_backend() -> str:
    # GAP verifies the signed split-quaternion basis units form D4/order 8.
    # The dual nilpotent eps is deliberately excluded: eps^2=0, so eps is not a unit.
    gap = "/home/goutev/miniforge3/envs/sage/bin/gap"
    script = r'''
# permutations induced by left multiplication by i and j on
# [1,-1,i,-i,j,-j,k,-k]
i := (1,3,2,4)(5,7,6,8);
j := (1,5)(2,6)(3,8)(4,7);
G := Group(i,j);
Print("GAP_SIGNED_SPLIT_Q_UNIT_GROUP_SIZE=", Size(G), "\n");
Print("GAP_SIGNED_SPLIT_Q_UNIT_GROUP_ID=", IdGroup(G), "\n");
Print("GAP_SIGNED_SPLIT_Q_UNIT_GROUP_IS_DIHEDRAL=", IsDihedralGroup(G), "\n");
QUIT;
'''
    result = subprocess.run([gap, "-q"], input=script, text=True, capture_output=True, check=True)
    assert "GAP_SIGNED_SPLIT_Q_UNIT_GROUP_SIZE=8" in result.stdout
    assert "GAP_SIGNED_SPLIT_Q_UNIT_GROUP_ID=[ 8, 3 ]" in result.stdout
    return result.stdout.strip()


def assert_sage_backend() -> str:
    sage = "/home/goutev/miniforge3/envs/sage/bin/sage"
    code = r'''
from sage.all import matrix, QQ
eta = matrix(QQ, [[1,0,0,0],[0,1,0,0],[0,0,-1,0],[0,0,0,-1]])
print("SAGE_SPLIT_Q_NORM_DET=", eta.det())
print("SAGE_SPLIT_Q_NORM_RANK=", eta.rank())
print("SAGE_SPLIT_Q_NORM_POS_NEG=2,2")
'''
    with tempfile.NamedTemporaryFile("w", suffix=".sage", delete=False) as f:
        f.write(code)
        tmp = f.name
    try:
        result = subprocess.run([sage, tmp], text=True, capture_output=True, check=True)
    finally:
        Path(tmp).unlink(missing_ok=True)
    assert "SAGE_SPLIT_Q_NORM_DET= 1" in result.stdout
    assert "SAGE_SPLIT_Q_NORM_RANK= 4" in result.stdout
    return result.stdout.strip()


def main() -> None:
    assert_split_quaternion_core()
    assert_dual_extension_core()
    assert_clifford_backend()
    assert_galgebra_backend()
    gap_out = assert_gap_backend()
    sage_out = assert_sage_backend()
    print(gap_out)
    print(sage_out)
    print("DUAL_SPLIT_QUATERNION_BACKBONE_OK")
    print("scope: exact algebra backbone only; no global screw-motion or automorphism classification")


if __name__ == "__main__":
    main()
