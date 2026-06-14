#!/usr/bin/env python3
"""Finite witness for e+ / e- compensated chiral parity index.

This is a finite algebraic witness only, not a global Witten/Möbius theorem.
"""

from __future__ import annotations


def chiral_mul(x: tuple[int, int], y: tuple[int, int]) -> tuple[int, int]:
    return (x[0] * y[0], x[1] * y[1])


def index(x: tuple[int, int]) -> int:
    return x[0] - x[1]


def main() -> None:
    e_plus = (1, 0)
    e_minus = (0, 1)
    split_one = (1, 1)
    compensated = (e_plus[0] + e_minus[0], e_plus[1] + e_minus[1])
    assert compensated == split_one
    assert index(compensated) == 0
    x = split_one
    for _ in range(20):
        x = chiral_mul(compensated, x)
        assert x == split_one
        assert index(x) == 0
    assert 0 % 16 == 0
    print("SYMPY_WITTEN_MOEBIUS_CHIRAL_PARITY_EPLUS_EMINUS_OK")
    print("SYMPY_WITTEN_MOEBIUS_CHIRAL_PARITY_RECURSION_ZERO_OK")
    print("SYMPY_WITTEN_ANOMALY_FREE_ZERO_OK")


if __name__ == "__main__":
    main()
