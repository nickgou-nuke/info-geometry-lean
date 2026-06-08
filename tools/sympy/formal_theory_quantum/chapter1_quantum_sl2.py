#!/usr/bin/env python3
"""Chapter 1 companion: finite fundamental representation of U_q(sl2)."""

from __future__ import annotations

import sympy as sp

from common import check, fundamental_uqsl2, mat_eq


def run() -> None:
    print("Chapter 1: U_q(sl2) finite representation")
    q = sp.symbols("q", nonzero=True)
    E, F, K, Kinv = fundamental_uqsl2(q)
    I = sp.eye(2)

    check("K K^-1 = I", mat_eq(K * Kinv, I))
    check("K^-1 K = I", mat_eq(Kinv * K, I))
    check("K E K^-1 = q^2 E", mat_eq(K * E * Kinv, q**2 * E))
    check("K F K^-1 = q^-2 F", mat_eq(K * F * Kinv, q**-2 * F))
    check("[E,F] = (K-K^-1)/(q-q^-1)", mat_eq(E * F - F * E, (K - Kinv) / (q - q**-1)))


if __name__ == "__main__":
    run()
