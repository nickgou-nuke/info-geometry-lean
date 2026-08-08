#!/usr/bin/env python3
"""Numerical witness for the non-Hermitian waveguide EP/braid specification.

This is an engineering-level sanity check, not a fabrication recipe.  Units are
`mm^{-1}` for propagation/coupling/gain-loss coefficients.

Model for a balanced two-waveguide gate:
    H = [[beta0 + i*dgamma/2, kappa],
         [kappa, beta0 - i*dgamma/2]]

EP condition:
    kappa^2 - (dgamma/2)^2 = 0  <=>  kappa = |dgamma|/2.

A loop around the EP is represented in coordinates `(delta_beta, gamma)` by
    delta_beta = r cos(phi), gamma = kappa + r sin(phi),
whose complex discriminant winds around zero once.
"""

from __future__ import annotations

import cmath
import math
import numpy as np


def h_eff(beta0: float, dgamma: float, kappa: float) -> np.ndarray:
    return np.array(
        [[beta0 + 0.5j * dgamma, kappa], [kappa, beta0 - 0.5j * dgamma]],
        dtype=complex,
    )


def ep_discriminant(dgamma: float, kappa: float) -> float:
    return kappa**2 - (dgamma / 2.0) ** 2


def winding_number(points: list[complex]) -> float:
    angles = np.unwrap(np.angle(np.array(points, dtype=complex)))
    return float((angles[-1] - angles[0]) / (2 * math.pi))


def loop_discriminant(kappa: float, radius: float, samples: int = 721) -> list[complex]:
    # Traceless two-level discriminant D = kappa^2 + (delta_beta + i*gamma)^2.
    # The EP is at delta_beta = 0, gamma = kappa.
    out: list[complex] = []
    for m in range(samples):
        phi = 2 * math.pi * m / (samples - 1)
        delta_beta = radius * math.cos(phi)
        gamma = kappa + radius * math.sin(phi)
        out.append(kappa**2 + (delta_beta + 1j * gamma) ** 2)
    return out


def main() -> int:
    beta0 = 10.0     # common propagation offset, mm^-1 (global phase)
    kappa = 0.20     # evanescent coupling, mm^-1
    dgamma_ep = 2 * kappa
    radius = 0.05    # loop radius in parameter plane, mm^-1

    H = h_eff(beta0, dgamma_ep, kappa)
    eigvals = np.linalg.eigvals(H)
    disc = ep_discriminant(dgamma_ep, kappa)
    loop = loop_discriminant(kappa, radius)
    wind = winding_number(loop)

    print("Non-Hermitian waveguide EP/braid specification witness")
    print(f"beta0       = {beta0:.3f} mm^-1")
    print(f"kappa       = {kappa:.3f} mm^-1")
    print(f"Delta gamma = {dgamma_ep:.3f} mm^-1")
    print(f"EP discriminant kappa^2-(Delta gamma/2)^2 = {disc:.3e}")
    print(f"EP eigenvalue coalescence residual = {abs(eigvals[0] - eigvals[1]):.3e}")
    print(f"Loop discriminant winding around zero ≈ {wind:.6f}")

    # Artin protocol length/gain budget sanity check.
    left = ["12", "23", "12"]
    right = ["23", "12", "23"]
    single_gate_gain = 1.03
    left_budget = single_gate_gain ** len(left)
    right_budget = single_gate_gain ** len(right)
    print(f"Left/right Artin protocol lengths: {len(left)} / {len(right)}")
    print(f"Length-only gain budgets: {left_budget:.9f} / {right_budget:.9f}")

    ok = (
        abs(disc) < 1e-12
        and abs(eigvals[0] - eigvals[1]) < 1e-6
        and abs(abs(wind) - 1.0) < 1e-2
        and abs(left_budget - right_budget) < 1e-12
    )
    if not ok:
        raise SystemExit("FAIL waveguide EP/braid witness")
    print("OK non-Hermitian waveguide EP/braid specification witness completed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
