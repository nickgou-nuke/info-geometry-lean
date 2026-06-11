#!/usr/bin/env python3
"""Numerical verifier for standard realizations of the Riemann zeta function.

This is an honest finite/numerical shadow only. It checks sample instances of:
- Dirichlet series
- Euler product
- Dirichlet eta relation
- Mellin integral
- completed xi symmetry / centered evenness
- Bernoulli special values
- Hurwitz specialization
- polylog specialization

It does NOT prove analytic continuation, global convergence, or RH.
"""

from __future__ import annotations

import math
import mpmath as mp
from sympy import bernoulli, primerange

mp.mp.dps = 80


def assert_close(a, b, tol: float, label: str) -> None:
    err = abs(a - b)
    if err > tol:
        raise AssertionError(f"{label}: err={err} > tol={tol}")


def dirichlet_partial(s, n_terms: int):
    return mp.fsum((n ** (-s) for n in range(1, n_terms + 1)))


def euler_product_partial(s, prime_bound: int):
    out = mp.mpf(1)
    for p in primerange(2, prime_bound + 1):
        out *= 1 / (1 - p ** (-s))
    return out


def eta_series(s):
    return mp.nsum(lambda n: (-1) ** (n - 1) / (n ** s), [1, mp.inf])


def mellin_zeta(s):
    f = lambda x: x ** (s - 1) / (mp.e ** x - 1)
    return mp.quad(f, [0, mp.inf]) / mp.gamma(s)


def xi(s):
    return mp.mpf("0.5") * s * (s - 1) * (mp.pi ** (-s / 2)) * mp.gamma(s / 2) * mp.zeta(s)


def main() -> None:
    # 1. Dirichlet series samples on Re(s) > 1.
    assert_close(dirichlet_partial(2, 20000), mp.zeta(2), 1e-4, "Dirichlet series at s=2")
    assert_close(dirichlet_partial(3, 5000), mp.zeta(3), 1e-6, "Dirichlet series at s=3")

    # 2. Euler product samples on Re(s) > 1.
    assert_close(euler_product_partial(2, 2000), mp.zeta(2), 5e-4, "Euler product at s=2")
    assert_close(euler_product_partial(3, 1000), mp.zeta(3), 5e-5, "Euler product at s=3")

    # 3. Eta relation.
    for s in [2, 3, 2 + 3j]:
        lhs = mp.zeta(s)
        rhs = eta_series(s) / (1 - 2 ** (1 - s))
        assert_close(lhs, rhs, 1e-10, f"eta relation at s={s}")

    # 4. Mellin integral at positive integers > 1.
    for s in [2, 4]:
        assert_close(mellin_zeta(s), mp.zeta(s), 1e-10, f"Mellin integral at s={s}")

    # 5. Completed xi symmetry and centered evenness.
    for s in [2 + 3j, 4 + 1j, mp.mpf('0.75') + 5j]:
        assert_close(xi(s), xi(1 - s), 1e-10, f"xi functional equation at s={s}")

    for z in [1 + 2j, mp.mpf('0.25') + 7j, -3 + 1j]:
        assert_close(xi(mp.mpf('0.5') + z), xi(mp.mpf('0.5') - z), 1e-10, f"centered xi evenness at z={z}")

    # 6. Bernoulli special values.
    for n in [0, 1, 3, 5]:
        rhs = -mp.mpf(str(bernoulli(n + 1))) / (n + 1)
        assert_close(mp.zeta(-n), rhs, 1e-30, f"Bernoulli special value at -{n}")

    # 7. Hurwitz specialization.
    for s in [2, 3, 2 + 3j]:
        assert_close(mp.zeta(s), mp.zeta(s, 1), 1e-12, f"Hurwitz specialization at s={s}")

    # 8. Polylog specialization on safe samples with Re(s) > 1.
    for s in [2, 3]:
        assert_close(mp.zeta(s), mp.polylog(s, 1), 1e-12, f"Polylog specialization at s={s}")

    print("===============================================================")
    print("STANDARD ZETA REALIZATIONS -- SYMPY VERIFICATION")
    print("===============================================================")
    print("  dirichlet series samples verified")
    print("  euler product samples verified")
    print("  dirichlet eta relation verified")
    print("  mellin integral samples verified")
    print("  completed xi symmetry and centered evenness verified")
    print("  bernoulli special values verified")
    print("  hurwitz and polylog specializations verified")
    print("  honest scope: finite/numerical samples only, not full analytic continuation")
    print("===============================================================")
    print("STANDARD ZETA REALIZATIONS VERIFIED")
    print("===============================================================")


if __name__ == "__main__":
    main()
