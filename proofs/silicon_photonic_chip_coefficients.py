#!/usr/bin/env python3
"""Engineering witness for silicon-photonic hyperbolic braid-gate coefficients.

This is a normalized coupled-mode calculation, not a foundry PDK.  Units:
- kappa: mm^-1
- length: mm
- alpha = kappa * length (dimensionless)

For the J-unitary hyperbolic scattering block
    S = [[cosh(alpha), sinh(alpha)], [sinh(alpha), cosh(alpha)]],
we report amplitudes and intensity coefficients:
    t = cosh(alpha), r = sinh(alpha), T=t^2, R=r^2.
Krein/SU(1,1) flux is T-R=1; ordinary Euclidean intensity has excess T+R-1.
"""

from __future__ import annotations

import math


def coefficients(kappa_mm_inv: float, length_mm: float) -> dict[str, float]:
    alpha = kappa_mm_inv * length_mm
    t = math.cosh(alpha)
    r = math.sinh(alpha)
    T = t * t
    R = r * r
    return {
        "kappa_mm_inv": kappa_mm_inv,
        "length_mm": length_mm,
        "alpha": alpha,
        "delta_gamma_ep_mm_inv": 2.0 * kappa_mm_inv,
        "transmission_amplitude": t,
        "reflection_amplitude": r,
        "transmittance": T,
        "reflectance": R,
        "krein_flux_balance_T_minus_R": T - R,
        "euclidean_budget_T_plus_R": T + R,
        "euclidean_defect_T_plus_R_minus_1": T + R - 1.0,
    }


def main() -> int:
    # Conservative normalized chip-scale examples.  Real devices should map these
    # through a foundry-specific dispersion/loss model.
    examples = [
        (0.05, 2.0),   # alpha=0.10: weak braid gate
        (0.10, 3.0),   # alpha=0.30: moderate gain/loss contrast
        (0.20, 2.5),   # alpha=0.50: strong hyperbolic gate
    ]

    print("Silicon photonic braid-gate coefficient witness")
    for kappa, length in examples:
        c = coefficients(kappa, length)
        print("\n---")
        print(f"kappa           = {c['kappa_mm_inv']:.4f} mm^-1")
        print(f"L               = {c['length_mm']:.4f} mm")
        print(f"alpha=kappa*L   = {c['alpha']:.4f}")
        print(f"EP Delta gamma  = {c['delta_gamma_ep_mm_inv']:.4f} mm^-1")
        print(f"t=cosh(alpha)   = {c['transmission_amplitude']:.9f}")
        print(f"r=sinh(alpha)   = {c['reflection_amplitude']:.9f}")
        print(f"T=t^2           = {c['transmittance']:.9f}")
        print(f"R=r^2           = {c['reflectance']:.9f}")
        print(f"T-R             = {c['krein_flux_balance_T_minus_R']:.12f}")
        print(f"T+R-1           = {c['euclidean_defect_T_plus_R_minus_1']:.9f}")
        if abs(c["krein_flux_balance_T_minus_R"] - 1.0) > 1e-12:
            raise SystemExit("FAIL Krein flux balance")

    print("\nOK silicon photonic chip coefficients witness completed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
