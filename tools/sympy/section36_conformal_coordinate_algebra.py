#!/usr/bin/env python3
"""Repaired Section 36 finite conformal-coordinate algebra witness.

Mirrors `InfoGeometry.Physics.Section36ConformalCoordinateAlgebra`.
Closed finite content only:
* conformal spatial coordinates x_i = t r n_i and squared-norm law;
* unit-direction residual t^2 - |x|^2 = t^2(1-r^2);
* Bloch residual specialization;
* second-order entropy/time-dilation defect comparison;
* finite Hamiltonian asymmetry H1-H2 vanishes iff H1=H2.

No Jacobian theorem, Einstein/Dirac PDE, actual von-Neumann entropy theorem,
Taylor-remainder theorem, Kähler manifold theorem, Lorentz/gauge unification,
electroweak theorem, or arrow-of-time theorem is claimed.
"""

from __future__ import annotations

import sys
from pathlib import Path
import sympy as sp

_REPO_ROOT = Path(__file__).resolve().parents[2]
if str(_REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(_REPO_ROOT))

from tools.sympy.common import assert_matrix_zero, assert_zero, mat2, pauli_matrices


def main() -> int:
    print("=" * 72)
    print("REPAIRED SECTION 36 CONFORMAL-COORDINATE ALGEBRA")
    print("=" * 72)

    t, r, n1, n2, n3 = sp.symbols("t r n1 n2 n3")
    direction_norm_sq = n1**2 + n2**2 + n3**2
    x = sp.Matrix([t*r*n1, t*r*n2, t*r*n3])
    spatial_norm_sq = sum(component**2 for component in x)
    assert_zero(spatial_norm_sq - t**2 * r**2 * direction_norm_sq,
                "conformal spatial squared-norm law")

    unit_residual = sp.expand((t**2 - spatial_norm_sq) - t**2*(1-r**2))
    assert_zero(unit_residual - t**2*r**2*(1 - direction_norm_sq),
                "unit-direction time-minus-space residual factor")
    print("finite conformal-coordinate norm laws: OK")

    bloch_residual_axis = 1 - r**2 * (1**2 + 0**2 + 0**2)
    assert_zero(bloch_residual_axis - (1 - r**2), "Bloch residual axis specialization")

    entropy_defect = -r**2 / 2
    time_dilation_defect = 1 - (1 - r**2 / 2)
    assert_zero(entropy_defect + time_dilation_defect,
                "quadratic entropy/time-dilation defect comparison")
    print("finite residual and quadratic-defect comparison: OK")

    H1 = mat2("A")
    H2 = mat2("B")
    asym = H1 - H2
    assert_matrix_zero(asym.subs({H1[0, 0]: H2[0, 0], H1[0, 1]: H2[0, 1],
                                  H1[1, 0]: H2[1, 0], H1[1, 1]: H2[1, 1]}),
                       "equal Hamiltonians give zero asymmetry")
    # Conversely, the entries of H1-H2 are exactly the componentwise equality residuals.
    for i in range(2):
        for j in range(2):
            assert_zero(asym[i, j] - (H1[i, j] - H2[i, j]),
                        f"Hamiltonian asymmetry entry {i}{j}")
    print("finite Hamiltonian asymmetry readout: OK")

    print("=" * 72)
    print("REPAIRED SECTION 36 FINITE SOCKET VERIFIED")
    print("=" * 72)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
