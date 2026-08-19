#!/usr/bin/env python3
"""Numerical checks for the corrected Ramanujan odd-zeta formula surface."""

from __future__ import annotations

import mpmath as mp
import sympy as sp

mp.mp.dps = 80


def bernoulli_factor(m: int) -> mp.mpf:
    return mp.mpf(str(sp.N(sp.bernoulli(m), 90))) / mp.factorial(m)


def lambert_series(n: int, alpha: mp.mpf) -> mp.mpf:
    exponent = 2 * n + 1
    return mp.nsum(
        lambda k: 1 / (mp.power(k, exponent) * mp.expm1(2 * alpha * k)),
        [1, mp.inf],
    )


def thermal_block(n: int, alpha: mp.mpf) -> mp.mpf:
    return mp.mpf("0.5") * mp.zeta(2 * n + 1) + lambert_series(n, alpha)


def modular_weight(n: int, alpha: mp.mpf) -> mp.mpf:
    return mp.power(alpha, -n)


def reflected_modular_weight(n: int, beta: mp.mpf) -> mp.mpf:
    return ((-1) ** n) * mp.power(beta, -n)


def bernoulli_anomaly_term(n: int, alpha: mp.mpf, beta: mp.mpf, k: int) -> mp.mpf:
    return (
        ((-1) ** k)
        * bernoulli_factor(2 * k)
        * bernoulli_factor(2 * n + 2 - 2 * k)
        * mp.power(alpha, n + 1 - k)
        * mp.power(beta, k)
    )


def bernoulli_anomaly(n: int, alpha: mp.mpf, beta: mp.mpf) -> mp.mpf:
    finite_sum = mp.fsum(bernoulli_anomaly_term(n, alpha, beta, k) for k in range(n + 2))
    return mp.power(2, 2 * n) * finite_sum


def ramanujan_lhs(n: int, alpha: mp.mpf) -> mp.mpf:
    return modular_weight(n, alpha) * thermal_block(n, alpha)


def ramanujan_rhs(n: int, alpha: mp.mpf, beta: mp.mpf) -> mp.mpf:
    return reflected_modular_weight(n, beta) * thermal_block(n, beta) - bernoulli_anomaly(
        n, alpha, beta
    )


def assert_close(lhs: mp.mpf, rhs: mp.mpf, label: str, tol: mp.mpf = mp.mpf("1e-45")) -> None:
    err = abs(lhs - rhs)
    if err > tol:
        raise AssertionError(f"{label}: |lhs-rhs|={err}\nlhs={lhs}\nrhs={rhs}")


def main() -> None:
    samples = [(1, mp.pi, mp.pi), (1, mp.pi / 2, 2 * mp.pi), (2, mp.pi / 3, 3 * mp.pi)]
    for n, alpha, beta in samples:
        assert n > 0 and alpha > 0 and beta > 0
        assert_close(alpha * beta, mp.pi**2, f"alpha*beta=pi^2 for n={n}")
        assert_close(
            mp.power(-beta, -n),
            reflected_modular_weight(n, beta),
            f"sign-factored reflected weight for n={n}",
        )
        assert_close(ramanujan_lhs(n, alpha), ramanujan_rhs(n, alpha, beta),
                     f"Ramanujan odd zeta transform n={n}")
    print("ramanujan_odd_zeta_interface: ok")


if __name__ == "__main__":
    main()
