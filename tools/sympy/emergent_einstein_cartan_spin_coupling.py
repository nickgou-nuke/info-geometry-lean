#!/usr/bin/env python3
"""Finite Einstein-Cartan spin-coupling bridge.

Mirrors
`lean/InfoGeometry/Canonical/EmergentEinsteinCartanSpinCoupling.lean`.

The check is strictly finite algebra:
* `T = kappa * beta * Spin` satisfies the torsion equation after absorbing
  `beta` into the spin-density readout;
* the torsion contraction and torsion norm scale by `(kappa*beta)^2`;
* the torsion-quadratic source therefore becomes the spin-quadratic source
  with coupling `alpha*(kappa*beta)^2`;
* the modified-Einstein residual expands to its spin-generated closed form.

No continuum variational calculus, Bianchi identity, diffeomorphism
invariance, spin bundle, or physical dynamics is claimed here.
"""

from __future__ import annotations

import sympy as sp


def assert_zero(expr, label: str) -> None:
    reduced = sp.expand(sp.simplify(expr))
    if reduced != 0:
        raise AssertionError(f"{label} failed:\n{reduced}")


def main() -> int:
    print("=" * 72)
    print("FINITE EINSTEIN-CARTAN SPIN COUPLING")
    print("=" * 72)

    alpha, kappa, beta, Lambda = sp.symbols("alpha kappa beta Lambda")
    scale = kappa * beta

    spin = {
        (lam, mu, nu): sp.symbols(f"S{lam}{mu}{nu}")
        for lam in range(2)
        for mu in range(2)
        for nu in range(2)
    }

    torsion = {key: scale * value for key, value in spin.items()}
    beta_spin = {key: beta * value for key, value in spin.items()}

    for key in spin:
        assert_zero(torsion[key] - kappa * beta_spin[key], "scaled spin torsion equation")
    print("  scaled spin torsion equation verified")

    def contraction(table, mu: int, nu: int):
        return sum(table[(mu, a, b)] * table[(nu, a, b)] for a in range(2) for b in range(2))

    def norm(table):
        return sum(table[(lam, a, b)] ** 2 for lam in range(2) for a in range(2) for b in range(2))

    for mu in range(2):
        for nu in range(2):
            assert_zero(
                contraction(torsion, mu, nu) - scale**2 * contraction(spin, mu, nu),
                f"quadratic contraction scaling ({mu},{nu})",
            )
    assert_zero(norm(torsion) - scale**2 * norm(spin), "torsion norm scaling")
    print("  quadratic torsion scaling verified")

    g00, g01, g10, g11 = sp.symbols("g00 g01 g10 g11")
    metric = {(0, 0): g00, (0, 1): g01, (1, 0): g10, (1, 1): g11}

    def theta(coupling, table, mu: int, nu: int):
        return 2 * coupling * (
            contraction(table, mu, nu)
            - sp.Rational(1, 4) * metric[(mu, nu)] * norm(table)
        )

    for mu in range(2):
        for nu in range(2):
            assert_zero(
                theta(alpha, torsion, mu, nu)
                - theta(alpha * scale**2, spin, mu, nu),
                f"spin-generated torsion source ({mu},{nu})",
            )
    print("  spin-generated torsion-quadratic source verified")

    G, H, Stress = {}, {}, {}
    for mu in range(2):
        for nu in range(2):
            G[(mu, nu)] = sp.symbols(f"G{mu}{nu}")
            H[(mu, nu)] = sp.symbols(f"H{mu}{nu}")
            Stress[(mu, nu)] = sp.symbols(f"Stress{mu}{nu}")

    for mu in range(2):
        for nu in range(2):
            spin_theta = theta(alpha * scale**2, spin, mu, nu)
            residual_from_scaled_torsion = (
                G[(mu, nu)]
                + Lambda * metric[(mu, nu)]
                + alpha * H[(mu, nu)]
                - kappa * (Stress[(mu, nu)] + theta(alpha, torsion, mu, nu))
            )
            closed_residual = (
                G[(mu, nu)]
                + Lambda * metric[(mu, nu)]
                + alpha * H[(mu, nu)]
                - kappa * (Stress[(mu, nu)] + spin_theta)
            )
            assert_zero(
                residual_from_scaled_torsion - closed_residual,
                f"spin-coupled modified-Einstein closed residual ({mu},{nu})",
            )
    print("  spin-coupled modified-Einstein closed residual verified")

    print("=" * 72)
    print("FINITE EINSTEIN-CARTAN SPIN COUPLING VERIFIED")
    print("=" * 72)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
