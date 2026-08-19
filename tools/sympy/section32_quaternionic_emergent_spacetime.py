#!/usr/bin/env python3
"""Repaired Section 32 finite quaternionic-emergent-spacetime witness.

This mirrors `InfoGeometry.Physics.Section32QuaternionicEmergentSpacetime`.
It checks only finite algebraic identities:
* corrected Pauli/quaternion sign obstruction;
* `t(I+r n·sigma)` equals `2t` times the radius-`r` Bloch density;
* determinant/Minkowski readout and null boundary certificate;
* scalar conformal covariance and quadratic determinant scaling;
* finite Lüders projection numerator support.

No theorem about emergent gravity, Einstein equations, torsion from spin,
entanglement/connection correspondence, black-hole information, or cosmology is
claimed here.
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
    print("REPAIRED SECTION 32 FINITE QUATERNIONIC SPACETIME INTERFACE")
    print("=" * 72)

    eye = sp.eye(2)
    sigma1 = sp.Matrix([[0, 1], [1, 0]])
    sigma2 = sp.Matrix([[0, -sp.I], [sp.I, 0]])
    sigma3 = sp.Matrix([[1, 0], [0, -1]])

    assert_matrix_zero((sp.I * sigma1) * (sp.I * sigma2) + sp.I * sigma3,
                       "literal k -> i sigma3 sign obstruction")
    assert_matrix_zero((sp.I * sigma1)**2 + eye, "qI square")
    assert_matrix_zero((sp.I * sigma2)**2 + eye, "qJ square")
    assert_matrix_zero((-sp.I * sigma3)**2 + eye, "corrected qK square")
    assert_matrix_zero((sp.I * sigma1) * (sp.I * sigma2) - (-sp.I * sigma3),
                       "corrected qI qJ = qK")
    print("corrected finite quaternion/Pauli signs: OK")

    t, r, n1, n2, n3, lam = sp.symbols("t r n1 n2 n3 lam")
    point = sp.Matrix([
        [t + t*r*n3, t*r*n1 - sp.I*t*r*n2],
        [t*r*n1 + sp.I*t*r*n2, t - t*r*n3],
    ])
    rho = sp.Matrix([
        [(1 + r*n3) / 2, (r*n1 - sp.I*r*n2) / 2],
        [(r*n1 + sp.I*r*n2) / 2, (1 - r*n3) / 2],
    ])
    assert_matrix_zero(point - 2*t*rho, "point equals 2t density")

    det_formula = t**2 * (1 - r**2 * (n1**2 + n2**2 + n3**2))
    assert_zero(point.det() - det_formula, "Bloch spacetime determinant")
    assert_zero(-point.det() - (-t**2 + (t*r*n1)**2 + (t*r*n2)**2 + (t*r*n3)**2),
                "Minkowski readout")
    null_det = sp.expand(det_formula.subs(n1**2 + n2**2 + n3**2, 1).subs(r**2, 1))
    assert_zero(null_det, "unit-boundary null determinant")
    print("density readback, determinant, and null boundary: OK")

    scaled_point = point.subs(t, lam*t)
    assert_matrix_zero(scaled_point - lam*point, "scalar conformal covariance")
    assert_zero(scaled_point.det() - lam**2 * point.det(), "quadratic determinant scaling")
    print("finite conformal scaling identities: OK")

    rho_generic = mat2("R")
    # Concrete nontrivial projector witness P^2=P.
    P = sp.Matrix([[1, 0], [0, 0]])
    assert_matrix_zero(P * (P * rho_generic * P) * P - P * rho_generic * P,
                       "Luders numerator projector support")
    print("finite Lüders numerator support: OK")

    print("=" * 72)
    print("REPAIRED SECTION 32 FINITE INTERFACE VERIFIED")
    print("=" * 72)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
