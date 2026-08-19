#!/usr/bin/env python3
"""Numerical shadow checks for SouriauTomitaZetaCenteredBridge.

Honest scope:
- checks the scalar three-channel centered Dirichlet factorization numerically;
- checks centered completed-Xi evenness and vanishing J-odd projection numerically;
- checks a toy discrete Gibbs/Souriau modular-potential identity numerically;
- checks a sample Ramanujan odd-zeta/Lambert transform identity numerically.

This script does not certify the broken untracked Lean file
`Arithmetic/ZetaSymmetryAdaptedDefinitions.lean`.
"""

from __future__ import annotations

import cmath
import math
import mpmath as mp


mp.mp.dps = 80


def assert_close(actual, expected, label: str, tol: float = 1e-40) -> None:
    err = abs(actual - expected)
    if err > tol:
        raise AssertionError(f"{label}: |actual-expected| = {err} > {tol}\nactual={actual}\nexpected={expected}")


def critical_line_weight(L: float) -> complex:
    return complex(mp.e ** (-(mp.mpf('0.5')) * L))


def scale_envelope(L: float, u: float) -> complex:
    return complex(mp.e ** (-u * L))


def phase_wave(L: float, v: float) -> complex:
    return complex(mp.e ** (-1j * v * L))


def centered_parameter(u: float, v: float) -> complex:
    return complex(0.5 + u, v)


def centered_dirichlet_mode(L: float, u: float, v: float) -> complex:
    return critical_line_weight(L) * scale_envelope(L, u) * phase_wave(L, v)


def completed_xi(s: complex) -> complex:
    s_mp = mp.mpc(s.real, s.imag)
    val = mp.mpf('0.5') * s_mp * (s_mp - 1) * (mp.pi ** (-s_mp / 2)) * mp.gamma(s_mp / 2) * mp.zeta(s_mp)
    return complex(val)


def centered_xi(z: complex) -> complex:
    return completed_xi(0.5 + z)


def j_odd_projection(F, z: complex) -> complex:
    return 0.5 * (F(z) - F(-z))


def ramanujan_lambert(n: int, alpha):
    return mp.nsum(
        lambda m: 1 / (mp.power(m, 2 * n + 1) * (mp.e ** (2 * m * alpha) - 1)),
        [1, mp.inf],
    )


def ramanujan_block(n: int, alpha):
    return mp.mpf('0.5') * mp.zeta(2 * n + 1) + ramanujan_lambert(n, alpha)


def bernoulli_number(k: int):
    return mp.bernoulli(k)


def ramanujan_rhs(n: int, alpha, beta):
    total = mp.mpf('0')
    for k in range(n + 2):
        coeff = ((-1) ** (k - 1)) * bernoulli_number(2 * k) * bernoulli_number(2 * n + 2 - 2 * k)
        denom = math.factorial(2 * k) * math.factorial(2 * n + 2 - 2 * k)
        total += coeff * (alpha ** (n + 1 - k)) * (beta ** k) / denom
    return (2 ** (2 * n)) * total


def check_centered_mode_factorization() -> None:
    samples = [
        (math.log(2.0), 0.0, 14.25),
        (math.log(3.0), 0.125, 7.0),
        (math.log(5.0), -0.2, -3.5),
    ]
    for L, u, v in samples:
        s = centered_parameter(u, v)
        lhs = cmath.exp(-s * L)
        rhs = centered_dirichlet_mode(L, u, v)
        assert_close(lhs, rhs, f"centered Dirichlet factorization at L={L}, u={u}, v={v}")
        if abs(u) < 1e-15:
            assert_close(scale_envelope(L, u), 1.0, f"critical-line dissipative channel at L={L}")
    print("centered scalar mode: three-channel factorization verified")


def check_centered_xi_jodd_zero() -> None:
    samples = [complex(0.0, 14.134725), complex(0.125, 9.0), complex(-0.2, 17.0)]
    for z in samples:
        assert_close(centered_xi(z), centered_xi(-z), f"centered Xi evenness at z={z}", tol=1e-18)
        assert_close(j_odd_projection(centered_xi, z), 0.0, f"centered Xi J-odd projection at z={z}", tol=1e-18)
    print("centered completed Xi: evenness and zero J-odd projection verified")


def check_toy_souriau_modular_potential() -> None:
    beta = mp.mpf('0.7')
    energies = [mp.mpf('0.0'), mp.mpf('1.0'), mp.mpf('2.5')]
    Z = mp.fsum(mp.e ** (-beta * e) for e in energies)
    Phi = mp.log(Z)
    rho = [mp.e ** (-beta * e - Phi) for e in energies]
    modular_potential = [-mp.log(r) for r in rho]
    target = [beta * e + Phi for e in energies]
    for i, (lhs, rhs) in enumerate(zip(modular_potential, target)):
        assert_close(complex(lhs), complex(rhs), f"toy Souriau modular potential at state {i}")
    entropy = mp.fsum(r * pot for r, pot in zip(rho, modular_potential))
    entropy_target = mp.fsum(r * (beta * e + Phi) for r, e in zip(rho, energies))
    assert_close(complex(entropy), complex(entropy_target), "toy entropy expectation identity")
    print("toy Souriau RN/modular-potential identity verified")


def check_ramanujan_interface_sample() -> None:
    samples = [
        (1, mp.pi, mp.pi),
        (1, mp.pi / 2, 2 * mp.pi),
    ]
    for n, alpha, beta in samples:
        lhs = alpha ** (-n) * ramanujan_block(n, alpha) - (-beta) ** (-n) * ramanujan_block(n, beta)
        rhs = ramanujan_rhs(n, alpha, beta)
        assert_close(complex(lhs), complex(rhs), f"Ramanujan odd-zeta interface sample n={n}", tol=1e-18)
    print("Ramanujan/Lambert interface sample verified")


if __name__ == "__main__":
    check_centered_mode_factorization()
    check_centered_xi_jodd_zero()
    check_toy_souriau_modular_potential()
    check_ramanujan_interface_sample()
    print("SOURIAU TOMITA ZETA CENTERED BRIDGE VERIFIED")
