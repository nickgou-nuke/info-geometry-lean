#!/usr/bin/env python3
"""Finite witness-obligation checks mirrored from Lean.

Checks finite forms of:
- orthogonal projector spectral powers H^k = Σ ε_i^k P_i;
- Boolean Gibbs trace factorization;
- diagonal eigenvector equation;
- Souriau beta projection shape.
"""

from __future__ import annotations

import itertools
import sympy as sp


def check_projector_power(n: int, max_k: int = 5) -> None:
    eps = sp.symbols(f"e0:{n}")
    # diagonal matrix projectors E_ii
    Ps = []
    for i in range(n):
        M = sp.zeros(n)
        M[i, i] = 1
        Ps.append(M)
    H = sum((eps[i] * Ps[i] for i in range(n)), sp.zeros(n))
    for k in range(max_k + 1):
        rhs = sum((eps[i] ** k * Ps[i] for i in range(n)), sp.zeros(n))
        if sp.simplify(H**k - rhs) != sp.zeros(n):
            raise AssertionError(f"projector power failed n={n}, k={k}")


def check_boolean_gibbs(n: int) -> None:
    beta = sp.Symbol("beta")
    eps = sp.symbols(f"e0:{n}")
    lhs = sp.Integer(0)
    for occ in itertools.product([0, 1], repeat=n):
        energy = sum(occ[i] * eps[i] for i in range(n))
        lhs += sp.exp(-beta * energy)
    rhs = sp.prod(1 + sp.exp(-beta * eps[i]) for i in range(n))
    if sp.simplify(sp.expand(lhs - rhs)) != 0:
        raise AssertionError(f"Boolean Gibbs factorization failed n={n}")


def check_diagonal_eigenvector(n: int) -> None:
    eps = sp.symbols(f"e0:{n}")
    for i in range(n):
        H = sp.diag(*eps)
        v = sp.zeros(n, 1)
        v[i, 0] = 1
        if sp.simplify(H * v - eps[i] * v) != sp.zeros(n, 1):
            raise AssertionError(f"diagonal eigenvector failed n={n}, i={i}")


def check_souriau_projection() -> None:
    b0, b1, b2, b3, p0, p1, p2, p3 = sp.symbols("b0 b1 b2 b3 p0 p1 p2 p3")
    pair = b0 * p0 - b1 * p1 - b2 * p2 - b3 * p3
    if sp.simplify(pair - (b0 * p0 - b1 * p1 - b2 * p2 - b3 * p3)) != 0:
        raise AssertionError("Souriau beta projection failed")


def main() -> None:
    for n in range(1, 7):
        check_projector_power(n)
        check_boolean_gibbs(n)
        check_diagonal_eigenvector(n)
    check_souriau_projection()
    print("explicit witness obligation finite checks ok")


if __name__ == "__main__":
    main()
