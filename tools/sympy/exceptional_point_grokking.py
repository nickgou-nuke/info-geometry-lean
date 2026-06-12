#!/usr/bin/env python3
"""SymPy twin for finite exceptional-point grokking algebra.

Verified here:
- a 2x2 Jordan block A = lambda I + N has a nonzero nilpotent deviation N;
- N^2 = 0;
- the characteristic polynomial has a repeated root lambda.

Not verified here:
- that real LLM training reaches this witness;
- that wallpaper topology forces an EP for arbitrary attention families;
- that hallucination is impossible or physically equivalent to Hawking radiation.
"""

from __future__ import annotations

import sympy as sp


def main() -> None:
    lam = sp.symbols("lambda")
    x = sp.symbols("x")

    N = sp.Matrix([[0, 1], [0, 0]])
    A = lam * sp.eye(2) + N
    deviation = A - lam * sp.eye(2)

    print("--- SymPy Twin: Exceptional-Point Grokking Algebra ---")
    print(f"Jordan block A:\n{A}")
    print(f"nilpotent deviation N:\n{deviation}")

    assert deviation == N
    assert N != sp.zeros(2, 2)
    assert N * N == sp.zeros(2, 2)
    print("nilpotent deviation is nonzero and square-zero: OK")

    charpoly = sp.factor(A.charpoly(x).as_expr())
    expected = (x - lam) ** 2
    assert sp.expand(charpoly - expected) == 0
    print(f"characteristic polynomial: {charpoly}")
    print("repeated eigenvalue lambda: OK")

    print("[SUCCESS] finite exceptional-point Jordan witness verified.")


if __name__ == "__main__":
    main()
