#!/usr/bin/env python3
"""SymPy witness for CoherentOrbitalPrecession.lean.

Audits the algebraic spine of tuchaki81/Coherent-Orbital-Precession:
Xi = e^2/(1-e^2) * r_g/a, delta = lambda_eff^2 Xi, corrected precession,
coherence tensor linearity, and table-scale predictions at lambda_eff = 1.95.
"""

import sympy as sp


def asymmetry_parameter(e, r_g, a):
    return sp.simplify(e**2 / (1 - e**2) * r_g / a)


def fractional_correction(lambda_eff, Xi):
    return sp.simplify(lambda_eff**2 * Xi)


def corrected_precession(precession_gr, lambda_eff, Xi):
    return sp.simplify(precession_gr * (1 + fractional_correction(lambda_eff, Xi)))


def gr_precession_per_orbit(G, M, c, a, e):
    return sp.simplify(6 * sp.pi * G * M / (c**2 * a * (1 - e**2)))


def coherence_tensor(lambda_coupling, hessian, box_phi, metric):
    return sp.simplify(lambda_coupling * (hessian - metric * box_phi))


if __name__ == "__main__":
    e, r_g, a, scale, lam, Xi, precession_gr = sp.symbols(
        "e r_g a scale lambda Xi precession_gr", nonzero=True
    )

    xi = asymmetry_parameter(e, r_g, a)
    xi_scaled = asymmetry_parameter(e, scale * r_g, scale * a)
    assert sp.simplify(xi_scaled - xi) == 0
    assert asymmetry_parameter(0, r_g, a) == 0
    assert fractional_correction(0, Xi) == 0
    assert corrected_precession(precession_gr, 0, Xi) == precession_gr

    lambda_bound = sp.Rational(195, 100)
    mercury_xi = sp.Rational(23, 10_000_000_000)
    s2_xi = sp.Rational(263, 1_000_000)
    inner_sstar_xi = sp.Rational(73, 10_000)

    mercury_delta = fractional_correction(lambda_bound, mercury_xi)
    s2_delta = fractional_correction(lambda_bound, s2_xi)
    inner_delta = fractional_correction(lambda_bound, inner_sstar_xi)

    print("Xi unit scaling invariant =", sp.simplify(xi_scaled - xi) == 0)
    print("lambda bound =", float(lambda_bound))
    print("Mercury delta at bound =", float(mercury_delta))
    print("S2 delta at bound =", float(s2_delta))
    print("Inner S-star delta at bound =", float(inner_delta))

    assert mercury_delta == sp.Rational(69966, 8_000_000_000_000)
    assert s2_delta == sp.Rational(400023, 400_000_000)
    assert inner_delta == sp.Rational(111033, 4_000_000)

    H = sp.Matrix(4, 4, lambda i, j: sp.Symbol(f"H{i}{j}"))
    g = sp.Matrix(4, 4, lambda i, j: sp.Symbol(f"g{i}{j}"))
    zero_tensor = coherence_tensor(0, H, sp.Symbol("box"), g)
    assert zero_tensor == sp.zeros(4, 4)

    print("zero-coupling coherence tensor = 0")
    print("Coherent orbital precession algebra audit passed")
