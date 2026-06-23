#!/usr/bin/env python3
"""Finite symbolic check for the Bayesian Markov chain interface."""

import sympy as sp


def require_zero(name: str, expr: sp.Expr) -> None:
    simplified = sp.factor(sp.cancel(expr))
    if simplified != 0:
        raise AssertionError(f"{name} failed: {simplified}")
    print(f"[ok] {name}")


def main() -> None:
    a, b = sp.symbols("a b", positive=True)
    p0, p1, l0, l1 = sp.symbols("p0 p1 l0 l1", positive=True)

    transition = sp.Matrix([[1 - a, a], [b, 1 - b]])
    stationary = sp.Matrix([[b / (a + b), a / (a + b)]])

    require_zero(
        "stationary Markov law",
        (stationary * transition - stationary)[0, 0],
    )
    require_zero(
        "stationary Markov law second component",
        (stationary * transition - stationary)[0, 1],
    )
    require_zero("detailed balance", stationary[0, 0] * a - stationary[0, 1] * b)
    require_zero("normalization", stationary[0, 0] + stationary[0, 1] - 1)

    prior_sum = p0 + p1
    prior0 = p0 / prior_sum
    prior1 = p1 / prior_sum
    evidence = prior0 * l0 + prior1 * l1
    posterior0 = prior0 * l0 / evidence
    posterior1 = prior1 * l1 / evidence

    require_zero("Bayes update normalization", posterior0 + posterior1 - 1)
    require_zero(
        "Bayes odds update",
        posterior0 / posterior1 - (p0 / p1) * (l0 / l1),
    )

    entropy_current = sp.log((stationary[0, 0] * a) / (stationary[0, 1] * b))
    require_zero("equilibrium entropy current", entropy_current)

    print("stationary =", [sp.simplify(stationary[0, i]) for i in range(2)])
    print("posterior =", [sp.simplify(posterior0), sp.simplify(posterior1)])


if __name__ == "__main__":
    main()
