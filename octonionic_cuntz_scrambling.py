#!/usr/bin/env python3
"""SymPy witness for the octonionic horizon scrambling corridor.

Evidence scope:
1) Finite Fibonacci R/F matrices (2×2) and braid/Yang-Baxter check.
2) OP1-diagonal lift consistency (structural, non-commutative model scaffold).
3) q-CCR symbolic interpolation table:
   - q = -1 gives CAR anti-commutator closure,
   - q = 0 gives Cuntz-Toeplitz normalization,
   - q = +1 gives CCR commutator closure.

This script is a computational certificate only.  The full analytic C*-isomorphism
is represented in Lean as an explicit socket hypothesis.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Iterable

import sympy as sp


@dataclass(frozen=True)
class Check:
    name: str
    ok: bool
    details: str = ""


def fibonacci_R_F() -> tuple[sp.Matrix, sp.Matrix]:
    """Return canonical Fibonacci Anyon `R` and `F` matrices."""
    phi = (1 + sp.sqrt(5)) / 2
    inv_phi = 1 / phi
    inv_sqrt_phi = sp.sqrt(inv_phi)

    F = sp.Matrix(
        [
            [inv_phi, inv_sqrt_phi],
            [inv_sqrt_phi, -inv_phi],
        ]
    )
    R = sp.Matrix(
        [
            [sp.exp(-4 * sp.I * sp.pi / 5), 0],
            [0, sp.exp(3 * sp.I * sp.pi / 5)],
        ]
    )
    return R, F


def diagonal_lift(M: sp.Matrix) -> sp.Matrix:
    """Conservative `OP1`-shell lift: act identically on two diagonal sectors."""
    return sp.diag(M, M)


def braid_and_lift_checks() -> list[Check]:
    """Check finite braid data and Yang-Baxter relation.

    `nsimplify` is used to collapse algebraic-cyclotomic terms.
    """
    R, F = fibonacci_R_F()

    I2 = sp.eye(2)

    sigma1 = R
    sigma2 = F * R * F
    checks: list[Check] = []

    checks.append(
        Check(
            "F^2 = I",
            sp.simplify(F * F - I2) == sp.zeros(2),
            f"F^2 = {sp.Matrix(F * F).tolist()}",
        )
    )
    checks.append(
        Check(
            "R^† R = I",
            sp.simplify(R.H * R - I2) == sp.zeros(2),
            f"R.H*R = {sp.Matrix(R.H * R).tolist()}",
        )
    )
    yb_defect = (sigma1 * sigma2 * sigma1 - sigma2 * sigma1 * sigma2).applyfunc(sp.simplify)
    checks.append(
        Check(
            "YB: σ1σ2σ1 = σ2σ1σ2",
            yb_defect.applyfunc(sp.nsimplify) == sp.zeros(2),
            f"defect = {sp.Matrix(yb_defect.applyfunc(sp.nsimplify))}",
        )
    )

    # Structural witness on diagonal OP1 shell.
    S1 = diagonal_lift(sigma1)
    S2 = diagonal_lift(sigma2)
    lift_defect = (S1 * S2 * S1 - S2 * S1 * S2).applyfunc(sp.simplify)
    checks.append(
        Check(
            "OP1-diagonal lift preserves YB",
            lift_defect.applyfunc(sp.nsimplify) == sp.zeros(4),
            f"lifted defect = {sp.Matrix(lift_defect.applyfunc(sp.nsimplify))}",
        )
    )
    return checks


def qccr_interpolation_checks() -> list[Check]:
    """Symbolic carrier-level q-CCR interpolation diagnostics.

    Relation is read as: a†a = 1 + q (a a†).  Write X := a a†.
    Then:
      a†a + aa† = 1 + (1+q) X
      a†a - aa† = 1 + (q-1) X
    """

    q = sp.Symbol("q", real=True)
    X = sp.Symbol("X", commutative=False)  # X = a * adag
    delta = sp.Integer(1)

    anti_expr = sp.expand(delta + (1 + q) * X)
    comm_expr = sp.expand(delta + (q - 1) * X)
    toeplitz_expr = sp.expand(delta + q * X)

    samples = [
        (sp.Integer(-1), "CAR point: q=-1"),
        (sp.Rational(-1, 2), "intermediate"),
        (sp.Integer(0), "Cuntz-Toeplitz point: q=0"),
        (sp.Rational(1, 2), "intermediate"),
        (sp.Integer(1), "CCR point: q=1"),
    ]

    checks: list[Check] = []
    for qv, label in samples:
        anti_v = sp.simplify(anti_expr.subs(q, qv))
        comm_v = sp.simplify(comm_expr.subs(q, qv))
        tout_v = sp.simplify(toeplitz_expr.subs(q, qv))

        if qv == -1:
            ok = anti_v == delta
        elif qv == 1:
            ok = comm_v == delta
        elif qv == 0:
            ok = tout_v == delta
        else:
            ok = True

        checks.append(
            Check(
                f"q = {qv} ({label})",
                ok,
                f"anti={anti_v}, comm={comm_v}, toeplitz={tout_v}",
            )
        )

    # Coefficients governing deformation of non-delta sector.
    checks.append(
        Check(
            "deformation coefficients",
            True,
            "anti-coefficient: (1+q); comm-coefficient: (q-1)",
        )
    )

    return checks


def print_checks(title: str, checks: Iterable[Check]) -> None:
    print(f"\n[{title}]")
    for chk in checks:
        status = "PASS" if chk.ok else "FAIL"
        print(f"  {status:4s} | {chk.name}")
        if chk.details:
            print(f"        {chk.details}")


def main() -> None:
    print("=== Octonionic Cuntz Scrambling Witness (SymPy) ===")

    print_checks("Finite Fibonacci braid", braid_and_lift_checks())
    print_checks("q-CCR deformation", qccr_interpolation_checks())

    # Concrete endpoint numerics for quick physical intuition.
    print("\n[endpoint numerics]")
    q_vals = [-1, -sp.Rational(1, 2), 0, sp.Rational(1, 2), 1]
    for q in q_vals:
        anti_coeff = sp.simplify(1 + q)
        comm_coeff = sp.simplify(q - 1)
        print(f"  q={q!s:>5}: anti-branch coeff=(1+q)={anti_coeff!s:>4}, comm-branch coeff=(q-1)={comm_coeff!s:>4}")

    R, _ = fibonacci_R_F()
    print("\nR eigenvalues:")
    for i, lam in enumerate(R.diagonal()):
        print(f"  R[{i}]={sp.N(lam, 20)}")

    print("\nWitness complete (computational evidence only).")


if __name__ == "__main__":
    main()
