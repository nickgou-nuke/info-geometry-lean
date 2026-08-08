#!/usr/bin/env python3
"""Finite log-potential branch selector for the non-isotropic Conf3 models."""

from __future__ import annotations

import math


def free_energy(beta: float, log_z: float) -> float:
    return -(1.0 / beta) * log_z


def entropy_from_uniform_rank(rank: int) -> float:
    return math.log(rank)


def renyi_uniform(rank: int, n: float) -> float:
    # Tr(rho^n) = rank * (1/rank)^n = rank^(1-n)
    return (1.0 / (1.0 - n)) * math.log(rank ** (1.0 - n))


def main() -> None:
    alpha_product_rank = 2**3
    flux_rank = 2**2
    product_rank = alpha_product_rank * flux_rank

    os_alpha_rank = 6
    os_flux_rank = os_alpha_rank * flux_rank

    assert product_rank == 32
    assert os_flux_rank == 24
    assert product_rank > os_flux_rank

    log_product = entropy_from_uniform_rank(product_rank)
    log_os = entropy_from_uniform_rank(os_flux_rank)
    assert log_product > log_os
    assert abs(log_product - (math.log(alpha_product_rank) + math.log(flux_rank))) < 1e-12

    beta = 2.0
    assert free_energy(beta, log_product) < free_energy(beta, log_os)

    for n in (0.5, 2.0, 3.0):
        assert abs(renyi_uniform(product_rank, n) - log_product) < 1e-12
        assert abs(renyi_uniform(os_flux_rank, n) - log_os) < 1e-12

    print("non_iso_conf3_log_potential_decision.py: log-potential selector passed")
    print("product/Leray rank, logZ =", product_rank, log_product)
    print("OS-alpha rank, logZ =", os_flux_rank, log_os)
    print("max entropy/log-rank branch: productLeray")


if __name__ == "__main__":
    main()
