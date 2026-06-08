#!/usr/bin/env python3
"""Chapter 8 companion: exact finite Fibonacci Artin/Yang-Baxter shadow."""

from __future__ import annotations

import sympy as sp

from common import check, fibonacci_groebner, matrix_zero_mod_fibonacci


def run() -> None:
    print("Chapter 8: finite hexagon/Yang-Baxter matrix shadow")
    q, a, s, gb = fibonacci_groebner()
    F = sp.Matrix([[a, s], [s, -a]])
    R = sp.diag(q**4, q**7)
    B = F * R * F

    check("F^2 = I modulo Fibonacci relations", matrix_zero_mod_fibonacci(F * F - sp.eye(2), gb))
    check("R B R = B R B modulo Fibonacci relations", matrix_zero_mod_fibonacci(R * B * R - B * R * B, gb))


if __name__ == "__main__":
    run()
