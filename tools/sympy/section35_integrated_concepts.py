#!/usr/bin/env python3
"""Repaired Section 35 finite integrated-concepts witness.

Mirrors `InfoGeometry.Physics.Section35IntegratedConcepts`.
Closed finite content only:
* `I + r n·σ = 2ρ` for the radius-r Bloch density;
* density and spacetime determinants share the residual
  `1 - r²(n1²+n2²+n3²)`;
* residual zero gives determinant-zero boundary certificates;
* finite biquaternion-pair dual conjugation is involutive, preserves a
  quadratic trace shadow, and flips a linear chiral-asymmetry readout.

No entropy/time-dilation, Planck discreteness, Kähler manifold, electroweak
chirality, Einstein equation, Dirac PDE, or physical emergence theorem is
claimed.
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
    print("REPAIRED SECTION 35 FINITE INTEGRATED CONCEPTS")
    print("=" * 72)

    sigma0 = sp.eye(2)
    sigma1 = sp.Matrix([[0, 1], [1, 0]])
    sigma2 = sp.Matrix([[0, -sp.I], [sp.I, 0]])
    sigma3 = sp.Matrix([[1, 0], [0, -1]])

    t, r, n1, n2, n3 = sp.symbols("t r n1 n2 n3")
    rho = sp.Matrix([
        [(1 + r*n3) / 2, (r*n1 - sp.I*r*n2) / 2],
        [(r*n1 + sp.I*r*n2) / 2, (1 - r*n3) / 2],
    ])
    spin_spacetime = sigma0 + r*n1*sigma1 + r*n2*sigma2 + r*n3*sigma3
    assert_matrix_zero(spin_spacetime - 2*rho, "spin-spacetime operator equals 2 density")

    residual = 1 - r**2 * (n1**2 + n2**2 + n3**2)
    point = sp.Matrix([
        [t + t*r*n3, t*r*n1 - sp.I*t*r*n2],
        [t*r*n1 + sp.I*t*r*n2, t - t*r*n3],
    ])
    assert_zero(rho.det() - sp.Rational(1, 4)*residual, "density determinant residual")
    assert_zero(point.det() - t**2*residual, "spacetime determinant residual")
    print("spin/density and residual determinant identities: OK")

    # Residual-zero boundary certificates are represented by divisibility by residual.
    assert_zero(rho.det() / residual - sp.Rational(1, 4), "density boundary coefficient")
    assert_zero(point.det() / residual - t**2, "spacetime boundary coefficient")
    print("residual-zero boundary certificates: OK")

    primal = mat2("P")
    dual = mat2("D")
    conj_primal = primal
    conj_dual = -dual
    conj2_primal = conj_primal
    conj2_dual = -conj_dual
    assert_matrix_zero(conj2_primal - primal, "dual conjugation primal involution")
    assert_matrix_zero(conj2_dual - dual, "dual conjugation dual involution")

    qtrace = sp.trace(primal*primal) + sp.trace(dual*dual)
    qtrace_conj = sp.trace(conj_primal*conj_primal) + sp.trace(conj_dual*conj_dual)
    asym = sp.trace(dual)
    asym_conj = sp.trace(conj_dual)
    assert_zero(qtrace_conj - qtrace, "quadratic trace dual-conj invariant")
    assert_zero(asym_conj + asym, "linear chiral asymmetry flips")
    print("finite biquaternion dual/chiral shadow: OK")

    print("=" * 72)
    print("REPAIRED SECTION 35 FINITE INTERFACE VERIFIED")
    print("=" * 72)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
