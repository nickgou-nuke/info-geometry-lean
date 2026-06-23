#!/usr/bin/env python3
"""Finite symbolic audit for the Bayesian Markov / discrete Hodge bridge."""

from __future__ import annotations

import sympy as sp


def require_zero(name: str, expr) -> None:
    simplified = sp.simplify(expr)
    if getattr(simplified, "shape", None) is not None:
        simplified = simplified.applyfunc(sp.simplify)
        if simplified != sp.zeros(*simplified.shape):
            raise AssertionError(f"{name} failed:\n{simplified}")
    elif simplified != 0:
        raise AssertionError(f"{name} failed: {simplified}")
    print(f"[ok] {name}")


def main() -> None:
    a, b = sp.symbols("a b", positive=True)
    p0, p1, l0, l1 = sp.symbols("p0 p1 l0 l1", positive=True)

    transition = sp.Matrix([[1 - a, a], [b, 1 - b]])
    stationary = sp.Matrix([[b / (a + b), a / (a + b)]])

    require_zero("stationary Markov law", stationary * transition - stationary)
    require_zero("detailed balance", stationary[0, 0] * a - stationary[0, 1] * b)

    prior0 = p0 / (p0 + p1)
    prior1 = p1 / (p0 + p1)
    evidence = prior0 * l0 + prior1 * l1
    posterior0 = prior0 * l0 / evidence
    posterior1 = prior1 * l1 / evidence
    require_zero("Bayes normalization", posterior0 + posterior1 - 1)

    d0 = sp.Matrix(
        [
            [-1, 1, 0],
            [0, -1, 1],
            [-1, 0, 1],
        ]
    )
    d1 = sp.Matrix([[-1, -1, 1]])
    harmonic = sp.Matrix([1, 1, -1])
    exact = d0 * sp.Matrix(sp.symbols("phi0 phi1 phi2"))

    require_zero("cochain condition", d1 * d0)
    require_zero("harmonic is coclosed", d0.T * harmonic)
    require_zero("harmonic is in kernel", (d0 * d0.T) * harmonic)
    require_zero("harmonic orthogonal exact", harmonic.dot(exact))

    filled_exact = d0 * sp.Matrix(sp.symbols("a b c"))
    filled_coexact = d1.T * sp.Matrix([sp.symbols("psi")])
    require_zero("filled exact/coexact orthogonality", filled_exact.dot(filled_coexact))

    print("stationary =", [sp.simplify(stationary[0, i]) for i in range(2)])
    print("harmonic =", harmonic.T)


if __name__ == "__main__":
    main()
