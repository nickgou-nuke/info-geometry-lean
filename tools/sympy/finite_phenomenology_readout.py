#!/usr/bin/env python3
"""Finite witness for the phenomenology readout dictionary.

Lean owner: `InfoGeometry.Canonical.FinitePhenomenologyReadout`.

The checks are intentionally finite:
* tripotent projector readouts for O = diag(0, 1, -1);
* Evans three-site harmonic trap invariance;
* Tomita swap even/odd decomposition for c+a and c-a;
* parity-invariant trace cancellation on a parity-odd matrix;
* finite S3 braid/Yang--Baxter permutation relation.

No continuum experiment, KMS/BEC transition, zeta theorem, or RH consequence is
claimed by this witness.
"""

from __future__ import annotations

import sympy as sp


def verify_trifactor_readout() -> None:
    O = sp.diag(0, 1, -1)
    I = sp.eye(3)
    P0 = I - O**2
    Pp = sp.Rational(1, 2) * (O**2 + O)
    Pm = sp.Rational(1, 2) * (O**2 - O)

    assert O**3 == O
    assert sp.simplify(P0 + Pp + Pm - I) == sp.zeros(3)
    assert O * P0 == sp.zeros(3)
    print("[1] tripotent null-sector readout verified")


def transition(left: str, right: str) -> tuple[str, str]:
    if (left, right) == ("+", "0"):
        return ("0", "+")
    if (left, right) == ("0", "-"):
        return ("-", "0")
    if (left, right) == ("+", "-"):
        return ("-", "+")
    return (left, right)


def verify_evans_trap() -> None:
    trap = ("-", "0", "+")

    left_pair = transition(trap[0], trap[1])
    right_pair = transition(trap[1], trap[2])

    assert (left_pair[0], left_pair[1], trap[2]) == trap
    assert (trap[0], right_pair[0], right_pair[1]) == trap
    print("[2] finite harmonic trap readout verified")


def verify_tomita_even_odd() -> None:
    c = sp.Matrix([1, 0])
    a = sp.Matrix([0, 1])
    J = sp.Matrix([[0, 1], [1, 0]])

    even = c + a
    odd = c - a

    assert J * even == even
    assert J * odd == -odd
    print("[3] Tomita even/odd ladder readout verified")


def verify_supertrace_cancellation() -> None:
    parity = sp.diag(1, -1)
    odd = sp.Matrix([[0, 1], [1, 0]])

    assert parity * odd * parity == -odd
    assert sp.trace(odd) == 0
    print("[4] parity-odd trace cancellation readout verified")


def verify_braid_readout() -> None:
    sigma1 = sp.Matrix([[0, 1, 0], [1, 0, 0], [0, 0, 1]])
    sigma2 = sp.Matrix([[1, 0, 0], [0, 0, 1], [0, 1, 0]])

    assert sigma1 * sigma2 * sigma1 == sigma2 * sigma1 * sigma2
    print("[5] finite braid/Yang-Baxter readout verified")


def main() -> None:
    print("=== FINITE PHENOMENOLOGY READOUT WITNESS ===")
    verify_trifactor_readout()
    verify_evans_trap()
    verify_tomita_even_odd()
    verify_supertrace_cancellation()
    verify_braid_readout()
    print("=== SUCCESS: FINITE READOUT DICTIONARY VERIFIED ===")


if __name__ == "__main__":
    main()
