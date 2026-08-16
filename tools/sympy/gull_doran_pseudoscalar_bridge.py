#!/usr/bin/env python3
"""
Finite Gull-Doran-Lasenby pseudoscalar bridge witness.

This mirrors lean/InfoGeometry/Clifford/GullDoranPseudoscalarBridge.lean.
It verifies the finite Pauli/Cl(3) pseudoscalar identities and their real
4 x 4 realification.  It does not model continuum STA, Maxwell equations,
Dirac spinors, or spectral/RH claims.
"""

import sys
from pathlib import Path
import sympy as sp

_REPO_ROOT = Path(__file__).resolve().parents[2]
if str(_REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(_REPO_ROOT))

from tools.sympy.common import assert_matrix_eq


def main() -> None:
    print("=" * 72)
    print("GULL-DORAN PSEUDOSCALAR BRIDGE -- SYMPY VERIFICATION")
    print("=" * 72)

    i = sp.I
    one2 = sp.eye(2)
    zero2 = sp.zeros(2)
    sigma1 = sp.Matrix([[0, 1], [1, 0]])
    sigma2 = sp.Matrix([[0, -i], [i, 0]])
    sigma3 = sp.Matrix([[1, 0], [0, -1]])

    for idx, sigma in enumerate((sigma1, sigma2, sigma3), start=1):
        assert_matrix_eq(sigma * sigma, one2, f"sigma{idx}^2 = I")

    assert_matrix_eq(sigma1 * sigma2 + sigma2 * sigma1, zero2, "{sigma1,sigma2}=0")
    assert_matrix_eq(sigma1 * sigma3 + sigma3 * sigma1, zero2, "{sigma1,sigma3}=0")
    assert_matrix_eq(sigma2 * sigma3 + sigma3 * sigma2, zero2, "{sigma2,sigma3}=0")

    pseudoscalar = sigma1 * sigma2 * sigma3
    assert_matrix_eq(pseudoscalar, i * one2, "sigma1 sigma2 sigma3 = i I")
    assert_matrix_eq(pseudoscalar * pseudoscalar, -one2, "pseudoscalar^2 = -I")
    print("  complex Pauli pseudoscalar verified")

    one4 = sp.eye(4)
    zero4 = sp.zeros(4)
    real_phase = sp.Matrix(
        [
            [0, -1, 0, 0],
            [1, 0, 0, 0],
            [0, 0, 0, -1],
            [0, 0, 1, 0],
        ]
    )
    real_sigma1 = sp.Matrix(
        [
            [0, 0, 1, 0],
            [0, 0, 0, 1],
            [1, 0, 0, 0],
            [0, 1, 0, 0],
        ]
    )
    real_sigma2 = sp.Matrix(
        [
            [0, 0, 0, 1],
            [0, 0, -1, 0],
            [0, -1, 0, 0],
            [1, 0, 0, 0],
        ]
    )
    real_sigma3 = sp.diag(1, 1, -1, -1)

    for idx, sigma in enumerate((real_sigma1, real_sigma2, real_sigma3), start=1):
        assert_matrix_eq(sigma * sigma, one4, f"real sigma{idx}^2 = I")

    assert_matrix_eq(real_sigma1 * real_sigma2 + real_sigma2 * real_sigma1, zero4, "real {s1,s2}=0")
    assert_matrix_eq(real_sigma1 * real_sigma3 + real_sigma3 * real_sigma1, zero4, "real {s1,s3}=0")
    assert_matrix_eq(real_sigma2 * real_sigma3 + real_sigma3 * real_sigma2, zero4, "real {s2,s3}=0")
    assert_matrix_eq(real_phase * real_phase, -one4, "real phase^2 = -I")
    assert_matrix_eq(real_sigma1 * real_sigma2 * real_sigma3, real_phase, "real pseudoscalar = phase")
    assert_matrix_eq(
        (real_sigma1 * real_sigma2 * real_sigma3) * (real_sigma1 * real_sigma2 * real_sigma3),
        -one4,
        "real pseudoscalar^2 = -I",
    )
    print("  real 4x4 pseudoscalar realification verified")

    print("=" * 72)
    print("GULL-DORAN PSEUDOSCALAR BRIDGE VERIFIED")
    print("=" * 72)


if __name__ == "__main__":
    main()
