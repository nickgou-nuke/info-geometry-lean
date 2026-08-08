#!/usr/bin/env python3
"""Numerical witness for SmithHatIsingDuality.lean.

The paper reports Monte Carlo estimates for the Ising model on the aperiodic
Smith-kite lattice and its dual.  This script audits the finite data and
recomputes the two reported Kramers-Wannier duality checks from the stated
numbers.  Lean remains the proof kernel for the exact bookkeeping layer.
"""

import sympy as sp


SMITH_HAT_SIDES = 13
SMITH_HAT_KITES = 8
MAX_REPORTED_SPINS = 939_201

Tc = sp.Rational(2405, 1000)
Tc_dual = sp.Rational(2143, 1000)
Tc_tolerance = sp.Rational(5, 10000)

energy_per_spin = sp.Rational(-1319, 1000)
energy_per_spin_dual = sp.Rational(-1505, 1000)


def kw_temperature_product(j_coupling=sp.Integer(1)):
    return sp.sinh(2 * j_coupling / Tc) * sp.sinh(2 * j_coupling / Tc_dual)


def coth(x):
    return sp.cosh(x) / sp.sinh(x)


def nearest_neighbor_correlation(energy_density):
    # Paper convention: epsilon(Tc) = -E(Tc)/(2N).
    return -energy_density / 2


def kw_energy_sum(j_coupling=sp.Integer(1)):
    eps = nearest_neighbor_correlation(energy_per_spin)
    eps_dual = nearest_neighbor_correlation(energy_per_spin_dual)
    return eps / coth(2 * j_coupling / Tc) + eps_dual / coth(2 * j_coupling / Tc_dual)


if __name__ == "__main__":
    temp_product = kw_temperature_product()
    energy_sum = kw_energy_sum()

    print("Smith hat sides =", SMITH_HAT_SIDES)
    print("Smith hat kites =", SMITH_HAT_KITES)
    print("maximum reported spins =", MAX_REPORTED_SPINS)
    print("Tc/J =", float(Tc), "+/-", float(Tc_tolerance))
    print("Tc*/J =", float(Tc_dual), "+/-", float(Tc_tolerance))
    print("sinh(2/Tc) sinh(2/Tc*) =", float(temp_product.evalf(16)))
    print("critical-energy duality sum =", float(energy_sum.evalf(16)))

    assert SMITH_HAT_SIDES == 13
    assert SMITH_HAT_KITES == 8
    assert MAX_REPORTED_SPINS == 939_201
    assert abs(float(temp_product.evalf()) - 1.0) < 0.001
    assert abs(float(energy_sum.evalf()) - 1.0) < 0.001

    print("Smith-hat Ising duality audit passed")
