#!/usr/bin/env python3
"""Finite witness for Horadam 2^k-ion recurrence and matrix methods.

Source: preprints201906.0303.v1, "Horadam 2^k-ions".

This verifies the theorem-safe coordinate layer:
  * Horadam scalar recurrence W_{n+2}=p W_{n+1}+q W_n;
  * finite vector/"2^k-ion" lift Ŵ_n=(W_n,...,W_{n+N-1});
  * componentwise recurrence Ŵ_{n+2}=p Ŵ_{n+1}+q Ŵ_n;
  * companion one-step matrix state update;
  * Horadam-ion matrix one-step update mirroring Theorem 8.

It deliberately does NOT formalize Cayley-Dickson multiplication,
nonassociativity, Binet identities over radicals, Catalan/Cassini identities, or
norm formulas. Those require later owner files.
"""

import sys
from pathlib import Path
import sympy as sp

_REPO_ROOT = Path(__file__).resolve().parents[2]
if str(_REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(_REPO_ROOT))

from tools.sympy.common import assert_matrix_eq


def horadam_values(a, b, p, q, count: int) -> list[sp.Expr]:
    vals = [sp.sympify(a), sp.sympify(b)]
    for n in range(count - 2):
        vals.append(sp.expand(p * vals[n + 1] + q * vals[n]))
    return vals[:count]


def ion(vals: list[sp.Expr], n: int, N: int) -> sp.Matrix:
    return sp.Matrix([vals[n + s] for s in range(N)])


def main() -> None:
    a, b, p, q = sp.Integer(2), sp.Integer(3), sp.Integer(5), sp.Integer(-2)
    N = 8  # octonion-sized coordinate packet; no octonion multiplication used.
    vals = horadam_values(a, b, p, q, 30)

    for n in range(0, 12):
        assert vals[n + 2] == p * vals[n + 1] + q * vals[n]
        assert_matrix_eq(
            f"ion recurrence n={n}",
            ion(vals, n + 2, N),
            p * ion(vals, n + 1, N) + q * ion(vals, n, N),
        )

    # Fundamental sequence U_n = W_n(0,1,p,q).
    U = horadam_values(0, 1, p, q, 30)
    M = sp.Matrix([[p, q], [1, 0]])
    for n in range(0, 12):
        state = sp.Matrix([U[n + 1], U[n]])
        next_state = sp.Matrix([U[n + 2], U[n + 1]])
        assert_matrix_eq(f"companion state n={n}", M * state, next_state)

    # Matrix packet M_W(n) = [[Ŵ_{n+2}, q Ŵ_{n+1}], [Ŵ_{n+1}, q Ŵ_n]].
    # Check componentwise against the 2x2 scalar companion matrix.
    for n in range(0, 8):
        for s in range(N):
            MWn_s = sp.Matrix([
                [vals[n + 2 + s], q * vals[n + 1 + s]],
                [vals[n + 1 + s], q * vals[n + s]],
            ])
            MWnext_s = sp.Matrix([
                [vals[n + 3 + s], q * vals[n + 2 + s]],
                [vals[n + 2 + s], q * vals[n + 1 + s]],
            ])
            assert_matrix_eq(f"Horadam-ion matrix step n={n} s={s}", MWn_s * M, MWnext_s)

    print("HORADAM_ION_MATRIX_METHODS_FINITE_OK")
    print("scope: coordinate recurrence and companion-matrix method only; no Cayley-Dickson product formalized")


if __name__ == "__main__":
    main()
