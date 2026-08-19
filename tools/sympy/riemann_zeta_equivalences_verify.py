#!/usr/bin/env python3
"""Numerical verifier for the Riemann-zeta equivalence corridor.

This mirrors `lean/InfoGeometry/Arithmetic/RiemannZetaEquivalences.lean`.
The Lean file proves:

* completed-xi parity in the symmetry-adapted coordinate,
* Euler product equality on `Re(s) > 1`, and
* Dirichlet-series equality on `Re(s) > 1`.

It keeps eta continuation and Ramanujan's odd-zeta transformation as
proof-carrying interfaces.  This script provides numerical checks for those
open analytic interfaces and checks that the executable series use the same
zero-mode-free and integer-parity conventions as the Lean definitions.
"""

from __future__ import annotations

import mpmath as mp
import sympy as sp

from ramanujan_odd_zeta_interface import (
    ramanujan_lhs,
    ramanujan_rhs,
    reflected_modular_weight,
)


mp.mp.dps = 70


def assert_close(lhs: complex, rhs: complex, label: str, tol: mp.mpf) -> None:
    err = abs(lhs - rhs)
    if err > tol:
        raise AssertionError(f"{label} failed: |lhs-rhs|={err}\nlhs={lhs}\nrhs={rhs}")


def completed_riemann_zeta(s: complex) -> complex:
    return mp.power(mp.pi, -s / 2) * mp.gamma(s / 2) * mp.zeta(s)


def riemann_xi(s: complex) -> complex:
    return mp.mpf("0.5") * s * (s - 1) * completed_riemann_zeta(s)


def eta_series_partial(s: complex, terms: int = 120000) -> complex:
    return mp.fsum(((-1) ** n) / mp.power(n + 1, s) for n in range(terms))


def dirichlet_series(s: complex, terms: int = 120000) -> complex:
    return mp.fsum(1 / mp.power(n + 1, s) for n in range(terms))


def euler_product(s: complex, prime_bound: int = 7000) -> complex:
    product = mp.mpc(1)
    for p in sp.primerange(2, prime_bound + 1):
        product *= 1 / (1 - mp.power(p, -s))
    return product


def eta_builtin(s: complex) -> complex:
    # SymPy owns the analytic-continuation oracle for this numerical witness.
    z = sp.Float(str(mp.re(s)), 90) + sp.I * sp.Float(str(mp.im(s)), 90)
    val = sp.N(sp.dirichlet_eta(z), 85)
    return mp.mpc(str(sp.re(val)), str(sp.im(val)))


def verify_positive_index_conventions() -> None:
    s = mp.mpc(2.4, 0.7)
    first_dirichlet_terms = [1 / mp.power(n + 1, s) for n in range(4)]
    first_eta_terms = [((-1) ** n) / mp.power(n + 1, s) for n in range(4)]

    assert_close(first_dirichlet_terms[0], 1, "Dirichlet first mode n=1", mp.mpf("1e-60"))
    assert first_eta_terms[0].real > 0
    assert first_eta_terms[1].real < 0
    assert first_eta_terms[2].real > 0
    assert first_eta_terms[3].real < 0


def verify_ramanujan_interface() -> None:
    samples = [
        (1, mp.pi, mp.pi),
        (1, mp.pi / 2, 2 * mp.pi),
        (2, mp.pi / 3, 3 * mp.pi),
    ]

    for n, alpha, beta in samples:
        assert_close(alpha * beta, mp.pi**2, f"Ramanujan alpha*beta n={n}", mp.mpf("1e-55"))
        assert_close(
            reflected_modular_weight(n, beta),
            ((-1) ** n) * mp.power(beta, -n),
            f"Ramanujan sign-factored beta weight n={n}",
            mp.mpf("1e-60"),
        )
        assert_close(
            ramanujan_lhs(n, alpha),
            ramanujan_rhs(n, alpha, beta),
            f"Ramanujan odd-zeta interface n={n}",
            mp.mpf("1e-45"),
        )


def verify_equivalences() -> None:
    print("RIEMANN ZETA EQUIVALENT REPRESENTATIONS -- SymPy/mpmath VERIFICATION")

    verify_positive_index_conventions()
    print("  positive-index conventions: checked")

    for z in [mp.mpc(0.2, 8.0), mp.mpc(-0.7, 3.25), mp.mpc(0.0, 14.1347251417347)]:
        assert_close(riemann_xi(mp.mpf("0.5") + z), riemann_xi(mp.mpf("0.5") - z),
                     "symmetry-adapted xi parity", mp.mpf("1e-45"))
    print("  completed xi parity: checked")

    s_eta = mp.mpc(0.7, 14.0)
    zeta_from_eta = eta_builtin(s_eta) / (1 - mp.power(2, 1 - s_eta))
    assert_close(zeta_from_eta, mp.zeta(s_eta), "eta quotient", mp.mpf("1e-35"))
    print("  eta quotient analytic-continuation witness: checked")

    s_eta_series = mp.mpc(2.4, 0.7)
    zeta_from_eta_series = eta_series_partial(s_eta_series) / (
        1 - mp.power(2, 1 - s_eta_series)
    )
    assert_close(
        zeta_from_eta_series,
        mp.zeta(s_eta_series),
        "eta positive-index alternating series",
        mp.mpf("5e-6"),
    )
    print("  eta positive-index alternating series: checked")

    s_conv = mp.mpc(2.4, 0.7)
    assert_close(dirichlet_series(s_conv), mp.zeta(s_conv), "Dirichlet series", mp.mpf("5e-6"))
    print("  Dirichlet series: checked")

    assert_close(euler_product(s_conv), mp.zeta(s_conv), "Euler product", mp.mpf("2e-5"))
    print("  Euler product: checked")

    verify_ramanujan_interface()
    print("  Ramanujan odd-zeta interface: checked")

    print("RIEMANN ZETA EQUIVALENCES VERIFIED")


if __name__ == "__main__":
    verify_equivalences()
