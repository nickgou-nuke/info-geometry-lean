#!/usr/bin/env python3
"""Chapter 8 companion: exact finite Fibonacci Artin/Yang-Baxter shadow."""

from __future__ import annotations

from common import (
    check,
    fibonacci_artin_factorization_holds,
    fibonacci_lean_artin_factorization_holds,
    fibonacci_norm_factorization_holds,
    fibonacci_yang_baxter_factorization_holds,
)


def run() -> None:
    print("Chapter 8: finite hexagon/Yang-Baxter matrix shadow")
    check("a^2 + s^2 = 1 cyclotomic factorization", fibonacci_norm_factorization_holds())
    check("scalar Artin constraint factorization", fibonacci_artin_factorization_holds())
    check("Lean Artin polynomial factorization", fibonacci_lean_artin_factorization_holds())
    check("R B R = B R B matrix-entry factorization", fibonacci_yang_baxter_factorization_holds())


if __name__ == "__main__":
    run()
