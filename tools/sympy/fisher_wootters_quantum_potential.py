#!/usr/bin/env python3
"""Fisher-Wootters Information Geometry, Anscombe Isometry & Madelung Wave Verification.

Mirrors:
  * `InfoGeometry.Canonical.FisherWoottersQuantumPotential`

Verifies:
  1. Fisher-Rao metric density for counting statistics: g_F(x) = 1/x
  2. Wootters / Anscombe differential isometry:
       4 * (d(sqrt(x))/dx)^2 = 4 * (1 / (2*sqrt(x)))^2 = 1/x = g_F(x)
  3. Madelung wave mode norm reconstruction:
       |Psi_gamma(x)|^2 = |sqrt(x) * (cos(gamma ln x) + i sin(gamma ln x))|^2 = x
  4. Geodesic Fisher distance:
       d_F(x1, x2) = 2 * |sqrt(x2) - sqrt(x1)|
       Collinear equality for 0 <= x1 <= x2 <= x3:
       d_F(x1, x2) + d_F(x2, x3) = d_F(x1, x3)
"""

from __future__ import annotations

import sys
from pathlib import Path
import sympy as sp

_REPO_ROOT = Path(__file__).resolve().parents[2]
if str(_REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(_REPO_ROOT))


def main() -> None:
    print("=" * 72)
    print("FISHER-WOOTTERS INFORMATION GEOMETRY & MADELUNG WAVE VERIFICATION")
    print("=" * 72)

    x, gamma = sp.symbols("x gamma", positive=True)

    # 1. Wootters Isometry
    psi = sp.sqrt(x)
    dpsi_dx = sp.diff(psi, x)
    expected_dpsi = 1 / (2 * sp.sqrt(x))
    assert sp.simplify(dpsi_dx - expected_dpsi) == 0
    metric_from_amplitude = 4 * dpsi_dx**2
    fisher_density = 1 / x
    assert sp.simplify(metric_from_amplitude - fisher_density) == 0
    print("  [OK] Wootters differential isometry 4 * (d(sqrt(x))/dx)^2 = 1/x = g_F(x) verified")

    # 2. Madelung Rotor and Wave Norm Reconstruction
    theta = gamma * sp.log(x)
    rotor_cos = sp.cos(theta)
    rotor_sin = sp.sin(theta)
    rotor_norm_sq = rotor_cos**2 + rotor_sin**2
    assert sp.simplify(rotor_norm_sq) == 1
    wave_norm_sq = (sp.sqrt(x))**2 * rotor_norm_sq
    assert sp.simplify(wave_norm_sq - x) == 0
    print("  [OK] Madelung wave norm reconstruction |Psi_gamma(x)|^2 = x verified")

    # 3. Geodesic Distance and Collinear Metric Property
    x1, x2, x3 = sp.symbols("x1 x2 x3", positive=True)
    d12 = 2 * (sp.sqrt(x2) - sp.sqrt(x1))
    d23 = 2 * (sp.sqrt(x3) - sp.sqrt(x2))
    d13 = 2 * (sp.sqrt(x3) - sp.sqrt(x1))
    assert sp.simplify((d12 + d23) - d13) == 0
    print("  [OK] Collinear Fisher geodesic distance triangle equality d_F(x1, x2) + d_F(x2, x3) = d_F(x1, x3) verified")

    print("=" * 72)
    print("FISHER-WOOTTERS INFORMATION GEOMETRY & MADELUNG WAVE VERIFIED")
    print("=" * 72)


if __name__ == "__main__":
    main()
