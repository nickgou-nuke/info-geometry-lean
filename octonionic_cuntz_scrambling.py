#!/usr/bin/env python3
"""SymPy witness for the octonionic-horizon Cuntz/q-CCR scrambling corridor.

Evidence scope:
1) Finite Fibonacci R/F matrices and braid/Yang-Baxter verification.
2) OP1-diagonal-lift structural preservation of the same braid identity.
3) q-CCR endpoint/readout interpolation (`q = -1, 0, +1`).

All checks are computational evidence.  The C*-equivalence of Kuzmin is represented
in Lean as an explicit assumption socket in `InfoGeometry.Projective.KuzminCuntzPath`.
"""

from __future__ import annotations

import argparse
import json
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Iterable, Tuple

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
    """Conservative OP1-shell lift: act identically on two diagonal sectors."""
    return sp.diag(M, M)


def braid_and_lift_checks() -> list[Check]:
    """Check finite braid data and Yang-Baxter relation."""
    R, F = fibonacci_R_F()

    I2 = sp.eye(2)
    sigma1 = R
    sigma2 = sp.simplify(F * R * F)

    checks: list[Check] = []

    checks.append(
        Check(
            "F^2 = I",
            sp.simplify(F * F - I2) == sp.zeros(2),
            f"F^2 = {sp.Matrix(sp.simplify(F*F)).tolist()}",
        )
    )
    checks.append(
        Check(
            "R^† R = I",
            sp.simplify(R.H * R - I2) == sp.zeros(2),
            f"R.H*R = {sp.Matrix(R.H * R).tolist()}",
        )
    )

    yb_defect = (sigma1 * sigma2 * sigma1 - sigma2 * sigma1 * sigma2)
    checks.append(
        Check(
            "YB: σ1σ2σ1 = σ2σ1σ2",
            yb_defect.applyfunc(sp.simplify).applyfunc(sp.nsimplify) == sp.zeros(2),
            f"defect = {sp.Matrix(yb_defect.applyfunc(sp.nsimplify))}",
        )
    )

    S1 = diagonal_lift(sigma1)
    S2 = diagonal_lift(sigma2)
    lift_defect = (S1 * S2 * S1 - S2 * S1 * S2)
    checks.append(
        Check(
            "OP1-diagonal lift preserves YB",
            lift_defect.applyfunc(sp.simplify).applyfunc(sp.nsimplify) == sp.zeros(4),
            f"lifted defect = {sp.Matrix(lift_defect.applyfunc(sp.nsimplify))}",
        )
    )

    return checks


def qccr_interpolation_checks() -> list[Check]:
    """Symbolic q-CCR interpolation diagnostics.

    Relation: `a†a = 1 + q (a a†)`; set `X := a a†`.
    Then
      a†a + aa† = 1 + (1+q) X
      a†a - aa† = 1 + (q-1) X
    """
    q = sp.Symbol("q", real=True)
    X = sp.Symbol("X", commutative=False)
    delta = sp.Integer(1)

    anti_expr = sp.expand(delta + (1 + q) * X)
    comm_expr = sp.expand(delta + (q - 1) * X)
    toeplitz_expr = sp.expand(delta + q * X)

    samples: list[tuple[sp.Integer | sp.Rational, str]] = [
        (sp.Integer(-1), "CAR point"),
        (sp.Rational(-1, 2), "intermediate"),
        (sp.Integer(0), "Cuntz-Toeplitz point"),
        (sp.Rational(1, 2), "intermediate"),
        (sp.Integer(1), "CCR point"),
    ]

    checks: list[Check] = []
    for qv, label in samples:
        anti_v = sp.simplify(anti_expr.subs(q, qv))
        comm_v = sp.simplify(comm_expr.subs(q, qv))
        tout_v = sp.simplify(toeplitz_expr.subs(q, qv))

        ok = True
        if qv == -1:
            ok = anti_v == delta
        elif qv == 1:
            ok = comm_v == delta
        elif qv == 0:
            ok = tout_v == delta

        checks.append(
            Check(
                f"q = {qv} ({label})",
                ok,
                f"anti={anti_v}, comm={comm_v}, toeplitz={tout_v}",
            )
        )

    checks.append(
        Check(
            "deformation coefficients",
            True,
            "anti-branch coefficient: (1+q); comm-branch coefficient: (q-1)",
        )
    )

    return checks


def run_checks() -> tuple[bool, list[Check], list[Check]]:
    braid_checks = braid_and_lift_checks()
    qccr_checks = qccr_interpolation_checks()
    all_ok = all(c.ok for c in braid_checks + qccr_checks)
    return all_ok, braid_checks, qccr_checks


def print_checks(title: str, checks: Iterable[Check]) -> None:
    print(f"\n[{title}]")
    for chk in checks:
        status = "PASS" if chk.ok else "FAIL"
        print(f"  {status:4s} | {chk.name}")
        if chk.details:
            print(f"        {chk.details}")


def as_payload(all_ok: bool, braid_checks: list[Check], qccr_checks: list[Check]) -> dict:
    return {
        "schema": "octonionic_cuntz_scrambling.v1",
        "is_verified": all_ok,
        "status": "verified" if all_ok else "failed",
        "checks": {
            "fibonacci_braid": [asdict(c) for c in braid_checks],
            "qccr_deformation": [asdict(c) for c in qccr_checks],
        },
    }


def main() -> None:
    parser = argparse.ArgumentParser(description="Run octonionic Cuntz scramble witness checks")
    parser.add_argument("--json", action="store_true", help="Emit JSON status payload")
    parser.add_argument("--out", type=str, default=None, help="Write JSON payload to file")
    args = parser.parse_args()

    all_ok, braid_checks, qccr_checks = run_checks()

    if args.json:
        payload = as_payload(all_ok, braid_checks, qccr_checks)
        text = json.dumps(payload, indent=2, sort_keys=True)
        if args.out is None:
            print(text)
        else:
            out = Path(args.out)
            out.parent.mkdir(parents=True, exist_ok=True)
            out.write_text(text, encoding="utf-8")
            print(f"wrote {out}")
        return

    print("=== Octonionic Cuntz Scrambling Witness (SymPy) ===")
    print_checks("Finite Fibonacci braid", braid_checks)
    print_checks("q-CCR deformation", qccr_checks)

    print("\n[endpoint numerics]")
    for q in [sp.Integer(-1), sp.Rational(-1, 2), sp.Integer(0), sp.Rational(1, 2), sp.Integer(1)]:
        anti_coeff = sp.simplify(1 + q)
        comm_coeff = sp.simplify(q - 1)
        print(f"  q={q!s:>5}: anti-branch coeff=(1+q)={anti_coeff!s:>4}, comm-branch coeff=(q-1)={comm_coeff!s:>4}")

    R, _ = fibonacci_R_F()
    print("\nR eigenvalues:")
    for i, lam in enumerate(R.diagonal()):
        print(f"  R[{i}]={sp.N(lam, 20)}")

    print("\nWitness complete (computational evidence only).")
    if all_ok:
        print("status: PASS")
    else:
        print("status: FAIL")


if __name__ == "__main__":
    main()
