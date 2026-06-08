#!/usr/bin/env python3
"""Chapter 5 companion: root-of-unity quantum integer shadow."""

from __future__ import annotations

import sympy as sp

from common import check, scalar_eq


def q_integer(n: int, q) -> sp.Expr:
    return sp.simplify((q**n - q**(-n)) / (q - q**-1))


def run() -> None:
    print("Chapter 5: roots of unity finite shadow")
    q = sp.exp(sp.I * sp.pi / 5)
    phi = (1 + sp.sqrt(5)) / 2

    check("q^5 = -1", scalar_eq(q**5, -1))
    check("q^10 = 1", scalar_eq(q**10, 1))
    check("[5]_q = 0", scalar_eq(q_integer(5, q), 0))
    check("2 cos(pi/5) = phi", scalar_eq(2 * sp.cos(sp.pi / 5), phi))
    for n in range(1, 5):
        check(f"[{n}]_q is nonzero numerically", abs(complex(sp.N(q_integer(n, q)))) > 1e-12)


if __name__ == "__main__":
    run()
