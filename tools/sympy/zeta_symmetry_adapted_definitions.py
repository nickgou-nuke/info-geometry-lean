#!/usr/bin/env python3
"""Symmetry-adapted zeta definitions and Ramanujan checks.

This mirrors
`lean/InfoGeometry/Arithmetic/ZetaSymmetryAdaptedDefinitions.lean`.

The script separates exact symbolic coordinate algebra from numerical analytic
checks.  It verifies sample instances of the equivalent zeta definitions and of
Ramanujan's odd-zeta transformation; it does not claim an analytic proof.
"""

from __future__ import annotations

import mpmath as mp
import sympy as sp


mp.mp.dps = 80


def assert_close(lhs: complex, rhs: complex, label: str, tol: mp.mpf = mp.mpf("1e-45")) -> None:
    err = abs(lhs - rhs)
    if err > tol:
        raise AssertionError(f"{label} failed: |lhs-rhs|={err}\nlhs={lhs}\nrhs={rhs}")


def assert_symbolic_zero(expr: sp.Expr, label: str) -> None:
    if sp.simplify(expr) != 0:
        raise AssertionError(f"{label} failed: {sp.simplify(expr)}")


def completed_lambda(s: complex) -> complex:
    return mp.power(mp.pi, -s / 2) * mp.gamma(s / 2) * mp.zeta(s)


def xi(s: complex) -> complex:
    return mp.mpf("0.5") * s * (s - 1) * completed_lambda(s)


def eta_series(s: complex, terms: int = 30000) -> complex:
    return mp.nsum(lambda k: (-1) ** (k - 1) / mp.power(k, s), [1, terms])


def dirichlet_series(s: complex, terms: int = 120000) -> complex:
    return mp.nsum(lambda k: 1 / mp.power(k, s), [1, terms])


def primes_upto(n: int) -> list[int]:
    return list(sp.primerange(2, n + 1))


def finite_euler_product(s: complex, prime_bound: int = 5000) -> complex:
    product = mp.mpc(1)
    for p in primes_upto(prime_bound):
        product *= 1 / (1 - mp.power(p, -s))
    return product


def bose_mellin_integral(s: complex) -> complex:
    f = lambda x: mp.power(x, s - 1) / mp.expm1(x)
    return mp.quad(f, [0, 1, mp.inf])


def theta(x: mp.mpf, terms: int = 80) -> mp.mpf:
    return mp.fsum(mp.e ** (-mp.pi * n * n * x) for n in range(-terms, terms + 1))


def bernoulli_number(n: int) -> mp.mpf:
    return mp.mpf(str(sp.N(sp.bernoulli(n), 90)))


def ramanujan_lambert(n: int, alpha: mp.mpf) -> mp.mpf:
    return mp.nsum(
        lambda m: 1 / (mp.power(m, 2 * n + 1) * (mp.e ** (2 * m * alpha) - 1)),
        [1, mp.inf],
    )


def ramanujan_block(n: int, alpha: mp.mpf) -> mp.mpf:
    return mp.mpf("0.5") * mp.zeta(2 * n + 1) + ramanujan_lambert(n, alpha)


def ramanujan_rhs(n: int, alpha: mp.mpf, beta: mp.mpf) -> mp.mpf:
    total = mp.mpf("0")
    for k in range(n + 2):
        total += (
            (-1) ** (k + 1)
            * bernoulli_number(2 * k)
            / mp.factorial(2 * k)
            * bernoulli_number(2 * n + 2 - 2 * k)
            / mp.factorial(2 * n + 2 - 2 * k)
            * alpha ** (n + 1 - k)
            * beta**k
        )
    return (2 ** (2 * n)) * total


def ramanujan_rhs_sympy(n: int, alpha: sp.Expr, beta: sp.Expr) -> sp.Expr:
    total = sp.Integer(0)
    for k in range(n + 2):
        total += (
            (-1) ** (k + 1)
            * sp.bernoulli(2 * k)
            / sp.factorial(2 * k)
            * sp.bernoulli(2 * n + 2 - 2 * k)
            / sp.factorial(2 * n + 2 - 2 * k)
            * alpha ** (n + 1 - k)
            * beta**k
        )
    return sp.simplify((2 ** (2 * n)) * total)


def check_coordinate_algebra() -> None:
    z, t = sp.symbols("z t")
    s_centered = sp.Rational(1, 2) + z
    s_critical = sp.Rational(1, 2) + sp.I * t
    assert_symbolic_zero((1 - s_centered) - (sp.Rational(1, 2) - z), "s=1/2+z reflection")
    assert_symbolic_zero((1 - s_critical) - (sp.Rational(1, 2) - sp.I * t), "critical-line reflection")

    s = sp.symbols("s")
    prefactor = sp.Rational(1, 2) * s * (s - 1)
    reflected_prefactor = sp.Rational(1, 2) * (1 - s) * ((1 - s) - 1)
    assert_symbolic_zero(prefactor - reflected_prefactor, "xi pole-removing prefactor")


def check_centered_xi_projector_bridge() -> None:
    u, v = sp.symbols("u v", real=True)

    def conjugation(point: tuple[sp.Expr, sp.Expr]) -> tuple[sp.Expr, sp.Expr]:
        return (point[0], -point[1])

    def functional_dual(point: tuple[sp.Expr, sp.Expr]) -> tuple[sp.Expr, sp.Expr]:
        return (-point[0], -point[1])

    def critical_mirror(point: tuple[sp.Expr, sp.Expr]) -> tuple[sp.Expr, sp.Expr]:
        return (-point[0], point[1])

    def same(left: tuple[sp.Expr, sp.Expr], right: tuple[sp.Expr, sp.Expr]) -> bool:
        return all(sp.simplify(a - b) == 0 for a, b in zip(left, right, strict=True))

    point = (u, v)
    assert same(conjugation(critical_mirror(point)), functional_dual(point))

    # Polynomial stand-in satisfying the same two hypotheses used in Lean:
    # Schwarz reflection and centered functional-equation invariance.
    xi_centered = 1 + u**2 + v**2 + sp.I * u * v
    j_xi = sp.conjugate(xi_centered.subs(u, -u))
    assert_symbolic_zero(j_xi - xi_centered, "centered xi J-invariance")

    even_projector = sp.simplify((xi_centered + j_xi) / 2)
    odd_projector = sp.simplify((xi_centered - j_xi) / 2)
    assert_symbolic_zero(even_projector - xi_centered, "P_J^+(xi)=xi")
    assert_symbolic_zero(odd_projector, "P_J^-(xi)=0")


def check_numeric_definitions() -> None:
    s = mp.mpc(2.4, 0.7)
    assert_close(dirichlet_series(s), mp.zeta(s), "Dirichlet series zeta(s)", mp.mpf("5e-6"))
    assert_close(finite_euler_product(s), mp.zeta(s), "Euler product zeta(s)", mp.mpf("2e-5"))

    seta = mp.mpc(0.7, 14.0)
    eta = eta_series(seta)
    eta_quotient = eta / (1 - mp.power(2, 1 - seta))
    assert_close(eta_quotient, mp.zeta(seta), "eta quotient continuation", mp.mpf("2e-4"))

    smellin = mp.mpf("2.5")
    assert_close(
        bose_mellin_integral(smellin),
        mp.gamma(smellin) * mp.zeta(smellin),
        "Mellin Bose kernel",
        mp.mpf("1e-40"),
    )

    x = mp.mpf("0.37")
    assert_close(theta(x), x ** (-mp.mpf("0.5")) * theta(1 / x), "theta modularity", mp.mpf("1e-50"))

    for sxi in [mp.mpc(0.3, 9.0), mp.mpc(1.7, -4.25), mp.mpc(0.5, 14.1347251417347)]:
        assert_close(xi(sxi), xi(1 - sxi), "completed xi functional symmetry", mp.mpf("1e-40"))


def check_ramanujan_odd_zeta() -> None:
    alpha, beta = sp.symbols("alpha beta")
    apery_defect = ramanujan_rhs_sympy(1, alpha, beta)
    expected_apery_defect = alpha**2 / 180 + alpha * beta / 36 + beta**2 / 180
    assert_symbolic_zero(apery_defect - expected_apery_defect, "zeta(3) Bernoulli defect")
    assert_symbolic_zero(
        apery_defect.subs(alpha * beta, sp.pi**2)
        - (alpha**2 / 180 + sp.pi**2 / 36 + beta**2 / 180),
        "zeta(3) Bernoulli defect under alpha beta = pi^2",
    )

    tau = sp.symbols("tau", nonzero=True)
    tau_defect = sp.simplify(apery_defect.subs({alpha: sp.pi * tau, beta: sp.pi / tau}))
    expected_tau_defect = sp.pi**2 * (tau**2 / 180 + sp.Rational(1, 36) + (1 / tau**2) / 180)
    assert_symbolic_zero(tau_defect - expected_tau_defect, "zeta(3) tau-defect")
    assert_symbolic_zero(
        tau_defect - tau_defect.subs(tau, 1 / tau),
        "zeta(3) tau-defect S-duality",
    )

    zeta5_defect = sp.factor(ramanujan_rhs_sympy(2, alpha, beta))
    expected_zeta5_defect = -(
        (alpha - beta) * (2 * alpha**2 + 9 * alpha * beta + 2 * beta**2) / 3780
    )
    assert_symbolic_zero(zeta5_defect - expected_zeta5_defect, "zeta(5) Bernoulli defect")
    zeta5_tau_defect = sp.factor(zeta5_defect.subs({alpha: sp.pi * tau, beta: sp.pi / tau}))
    expected_zeta5_tau_defect = -sp.pi**3 * (
        (tau - 1) * (tau + 1) * (2 * tau**4 + 9 * tau**2 + 2) / (3780 * tau**3)
    )
    assert_symbolic_zero(zeta5_tau_defect - expected_zeta5_tau_defect, "zeta(5) tau-defect")
    assert_symbolic_zero(
        zeta5_tau_defect + zeta5_tau_defect.subs(tau, 1 / tau),
        "zeta(5) tau-defect S-anti-duality",
    )

    zeta7_defect = sp.factor(ramanujan_rhs_sympy(3, alpha, beta))
    expected_zeta7_defect = (
        (alpha**2 - alpha * beta + beta**2)
        * (3 * alpha**2 + 13 * alpha * beta + 3 * beta**2)
        / 56700
    )
    assert_symbolic_zero(zeta7_defect - expected_zeta7_defect, "zeta(7) Bernoulli defect")
    zeta7_tau_defect = sp.factor(zeta7_defect.subs({alpha: sp.pi * tau, beta: sp.pi / tau}))
    expected_zeta7_tau_defect = sp.pi**4 * (
        (tau**4 - tau**2 + 1) * (3 * tau**4 + 13 * tau**2 + 3) / (56700 * tau**4)
    )
    assert_symbolic_zero(zeta7_tau_defect - expected_zeta7_tau_defect, "zeta(7) tau-defect")
    assert_symbolic_zero(
        zeta7_tau_defect - zeta7_tau_defect.subs(tau, 1 / tau),
        "zeta(7) tau-defect S-duality",
    )

    zeta9_defect = sp.factor(ramanujan_rhs_sympy(4, alpha, beta))
    expected_zeta9_defect = -(
        (alpha - beta)
        * (
            10 * alpha**4
            + 43 * alpha**3 * beta
            + 21 * alpha**2 * beta**2
            + 43 * alpha * beta**3
            + 10 * beta**4
        )
        / 1871100
    )
    assert_symbolic_zero(zeta9_defect - expected_zeta9_defect, "zeta(9) Bernoulli defect")
    zeta9_tau_defect = sp.factor(zeta9_defect.subs({alpha: sp.pi * tau, beta: sp.pi / tau}))
    expected_zeta9_tau_defect = -sp.pi**5 * (
        (tau - 1)
        * (tau + 1)
        * (10 * tau**8 + 43 * tau**6 + 21 * tau**4 + 43 * tau**2 + 10)
        / (1871100 * tau**5)
    )
    assert_symbolic_zero(zeta9_tau_defect - expected_zeta9_tau_defect, "zeta(9) tau-defect")
    assert_symbolic_zero(
        zeta9_tau_defect + zeta9_tau_defect.subs(tau, 1 / tau),
        "zeta(9) tau-defect S-anti-duality",
    )

    samples = [
        (1, mp.pi, mp.pi),
        (1, mp.pi / 2, 2 * mp.pi),
        (2, mp.pi / 3, 3 * mp.pi),
        (3, mp.pi / 4, 4 * mp.pi),
        (4, mp.pi / 5, 5 * mp.pi),
    ]
    for n, alpha, beta in samples:
        lhs = alpha ** (-n) * ramanujan_block(n, alpha) - (-beta) ** (-n) * ramanujan_block(n, beta)
        rhs = ramanujan_rhs(n, alpha, beta)
        assert_close(lhs, rhs, f"Ramanujan zeta({2*n+1}) transform", mp.mpf("1e-45"))


def main() -> None:
    print("=" * 78)
    print("ZETA SYMMETRY-ADAPTED DEFINITIONS -- SYMPY/MPMATH VERIFIER")
    print("=" * 78)
    check_coordinate_algebra()
    print("  coordinate algebra: s=1/2+z makes reflection parity")
    check_centered_xi_projector_bridge()
    print("  centered xi projector bridge: J-even implies P_J^-(xi)=0")
    check_numeric_definitions()
    print("  equivalent zeta definitions: Dirichlet/Euler/eta/Mellin/theta/xi checked")
    check_ramanujan_odd_zeta()
    print("  Ramanujan zeta(3) Bernoulli defect: exact quadratic checked")
    print("  Ramanujan zeta(3) tau-defect: tau <-> 1/tau symmetry checked")
    print("  Ramanujan zeta(5) tau-defect: tau <-> 1/tau anti-symmetry checked")
    print("  Ramanujan zeta(7) tau-defect: tau <-> 1/tau symmetry checked")
    print("  Ramanujan zeta(9) tau-defect: tau <-> 1/tau anti-symmetry checked")
    print("  Ramanujan odd-zeta transformation: numerical samples passed")
    print("=" * 78)
    print("ZETA SYMMETRY-ADAPTED DEFINITIONS VERIFIED")
    print("=" * 78)


if __name__ == "__main__":
    main()
