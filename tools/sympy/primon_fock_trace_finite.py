#!/usr/bin/env python3
"""
Finite primon Fock trace identity (SymPy mirror of Lean formalization).

For Boolean occupations b_i ∈ {0,1} and diagonal Hamiltonian
    H(b) = Σ_i b_i ε_i,
the finite Gibbs trace factors as
    Σ_b exp(-β H(b)) = Π_i (1 + exp(-β ε_i)).

This is finite algebra only: no infinite Euler product, analytic continuation,
or RH claim.
"""

from __future__ import annotations

import argparse
import itertools
import sympy as sp


def fock_energy(bits: tuple[int, ...], eps: tuple[sp.Symbol, ...]) -> sp.Expr:
    return sum(b * e for b, e in zip(bits, eps))


def trace_sum(n: int, beta: sp.Symbol, eps: tuple[sp.Symbol, ...]) -> sp.Expr:
    return sum(
        sp.exp(-beta * fock_energy(bits, eps))
        for bits in itertools.product([0, 1], repeat=n)
    )


def product_formula(n: int, beta: sp.Symbol, eps: tuple[sp.Symbol, ...]) -> sp.Expr:
    out = sp.Integer(1)
    for e in eps:
        out *= 1 + sp.exp(-beta * e)
    return sp.expand(out)


def verify(n: int) -> bool:
    beta = sp.Symbol("beta")
    eps = sp.symbols(f"eps0:{n}")
    lhs = sp.expand(trace_sum(n, beta, eps))
    rhs = product_formula(n, beta, eps)
    return sp.simplify(lhs - rhs) == 0


def prime_specialization(n: int) -> sp.Expr:
    beta = sp.Symbol("beta")
    primes = list(sp.primerange(1, 100))[:n]
    return sp.prod(1 + sp.exp(-beta * sp.log(p)) for p in primes)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--max-n", type=int, default=6)
    args = parser.parse_args()

    for n in range(args.max_n + 1):
        ok = verify(n)
        print(f"n={n}: trace factorization {'ok' if ok else 'FAIL'}")
        if not ok:
            raise SystemExit(1)

    print("prime specialization example n=4:")
    print(prime_specialization(4))


if __name__ == "__main__":
    main()
