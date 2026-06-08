#!/usr/bin/env python3
"""Chapter 4 companion: braid operator from swap composed with R."""

from __future__ import annotations

import sympy as sp

from common import braid_Rcheck_fundamental, check, kron, mat_eq


def run() -> None:
    print("Chapter 4: braided category finite shadow")
    q = sp.symbols("q", nonzero=True)
    I = sp.eye(2)
    Rcheck = braid_Rcheck_fundamental(q)
    B12 = kron(Rcheck, I)
    B23 = kron(I, Rcheck)

    check("braid operator is invertible", Rcheck.det() != 0)
    check("B12 B23 B12 = B23 B12 B23", mat_eq(B12 * B23 * B12, B23 * B12 * B23))


if __name__ == "__main__":
    run()
