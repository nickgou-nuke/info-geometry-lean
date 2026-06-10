#!/usr/bin/env python3
"""Finite Mellin/Dirichlet convolution + zeta-coordinate symmetry verifier.

This script deliberately mirrors the theorem-safe Lean bridge:

1. finite Möbius Dirichlet polynomial = finite fermionic Euler product;
2. divisor Möbius cancellation gives the delta at n=1;
3. squarefree parity agrees with the Möbius sign / Liouville sign on the
   squarefree lane;
4. the antiunitary critical mirror fixes exactly sigma = 1/2, and the centered
   coordinate turns the fixed locus into u = 0.

No infinite convergence, analytic continuation, or RH claim is made here.
"""

from __future__ import annotations

import itertools
from math import prod

import sympy as sp
from sympy import mobius
from sympy.ntheory import divisors, factorint


sigma, tau = sp.symbols("sigma tau", real=True)
point = (sigma, tau)


def euler_product(primes: list[int], q) -> sp.Expr:
    out = sp.Integer(1)
    for p in primes:
        out *= 1 - q(p)
    return sp.expand(out)


def mobius_dirichlet_polynomial(primes: list[int], q) -> sp.Expr:
    total = sp.Integer(0)
    for r in range(len(primes) + 1):
        for subset in itertools.combinations(primes, r):
            n = prod(subset) if subset else 1
            weight = sp.Integer(1)
            for p in subset:
                weight *= q(p)
            total += mobius(n) * weight
    return sp.expand(total)


def squarefree_parity_sign(n: int) -> int:
    fac = factorint(n)
    if any(exp != 1 for exp in fac.values()):
        raise ValueError(f"n={n} is not squarefree")
    return (-1) ** len(fac)


def conjugation(p):
    s, t = p
    return (s, -t)


def functional_dual(p):
    s, t = p
    return (1 - s, -t)


def critical_mirror(p):
    s, t = p
    return (1 - s, t)


def centered(p):
    s, t = p
    return (s - sp.Rational(1, 2), t)


def same(p, q) -> bool:
    return all(sp.simplify(a - b) == 0 for a, b in zip(p, q, strict=True))


def main() -> None:
    print("mellin_dirichlet_convolution_symmetry: start")

    primes = [2, 3, 5]
    q = lambda p: sp.Symbol(f"q{p}")

    poly = mobius_dirichlet_polynomial(primes, q)
    euler = euler_product(primes, q)
    assert sp.expand(poly - euler) == 0
    print("  finite_mobius_dirichlet_equals_euler_product: ok")
    print(f"    primes = {primes}")
    print(f"    polynomial = {poly}")

    delta_values: dict[int, int] = {}
    for n in range(1, 21):
        delta_values[n] = int(sum(mobius(d) for d in divisors(n)))
        expected = 1 if n == 1 else 0
        assert delta_values[n] == expected
    print("  divisor_sum_mobius_equals_delta: ok")
    print(f"    first_values = {delta_values}")

    squarefree_samples = [1, 2, 3, 5, 6, 10, 15, 30]
    for n in squarefree_samples:
        mu = int(mobius(n))
        parity = 1 if n == 1 else squarefree_parity_sign(n)
        assert mu == parity
    print("  squarefree_parity_equals_mobius_sign: ok")

    liouville_samples = [1, 2, 3, 4, 6, 12, 30]
    liouville_report = {}
    for n in liouville_samples:
        factorization = factorint(n)
        omega = sum(factorization.values())
        liouville = (-1) ** omega
        liouville_report[n] = liouville
        is_squarefree = all(exp == 1 for exp in factorization.values())
        if is_squarefree:
            assert liouville == int(mobius(n))
    print("  liouville_matches_mobius_on_squarefree_lane: ok")
    print(f"    liouville_samples = {liouville_report}")

    c = conjugation
    f = functional_dual
    j = critical_mirror
    assert same(c(c(point)), point)
    assert same(f(f(point)), point)
    assert same(j(j(point)), point)
    assert same(f(c(point)), c(f(point)))
    assert same(j(point), f(c(point)))

    u, v = centered(point)
    assert same(centered(j(point)), (-u, v))
    fixed_solution = sp.solve(
        [sp.Eq(j(point)[0], point[0]), sp.Eq(j(point)[1], point[1])],
        [sigma],
        dict=True,
    )
    assert fixed_solution == [{sigma: sp.Rational(1, 2)}]
    assert sp.simplify(u.subs(sigma, sp.Rational(1, 2))) == 0
    print("  affine_symmetry_frame_and_fixed_locus: ok")
    print("    critical_mirror_fixed_locus = sigma = 1/2")
    print("    centered_coordinate = u = sigma - 1/2")

    print("mellin_dirichlet_convolution_symmetry: ok")


if __name__ == "__main__":
    main()
