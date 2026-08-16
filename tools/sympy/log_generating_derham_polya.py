#!/usr/bin/env python3
"""Log-Generating Coordinates, de Rham Log-Forms & Hilbert-Pólya SymPy Verification.

Mirrors:
  * `InfoGeometry.Topology.LogGeneratingDeRhamPolyaBridge`

Verifies:
  1. Scale Invariance of de Rham Log-Form:
       d(lambda * z) / (lambda * z) = dz / z
  2. Scale Vector Field Identity:
       z * d/dz (z^{-s}) = -s * z^{-s}  <===>  d/dtau (e^{-s tau}) = -s * e^{-s tau}
  3. Hilbert-Pólya Eigenvalue Inversion:
       H = -i (z d/dz + 1/2) = -i (d/dtau + 1/2)
       H (z^{-s}) = -i (-s + 1/2) z^{-s} = i (s - 1/2) z^{-s} = E z^{-s}
       E(s) = i(s - 1/2),  s(E) = 1/2 - i E
  4. Spectral Reality <===> Critical Line:
       Im(E) = 0  <===>  Re(s) = 1/2
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
    print("LOG-GENERATING COORDINATES, DE RHAM LOG-FORMS & HILBERT-PÓLYA VERIFICATION")
    print("=" * 72)

    # 1. Scale Invariance of de Rham Logarithmic 1-Form
    z = sp.Symbol("z", positive=True)
    lam = sp.Symbol("lambda", positive=True)
    dz = sp.Symbol("dz")

    # (lambda dz) / (lambda z) == dz / z
    scaled_form = (lam * dz) / (lam * z)
    canonical_form = dz / z
    assert sp.simplify(scaled_form - canonical_form) == 0
    print("  [OK] Scale invariance of de Rham logarithmic 1-form dz/z verified")

    # 2. Scale generator action in log coordinates tau = ln z
    tau = sp.Symbol("tau", real=True)
    s = sp.Symbol("s")

    psi_tau = sp.exp(-s * tau)
    dpsi_dtau = sp.diff(psi_tau, tau)
    # d/dtau (e^{-s tau}) = -s e^{-s tau}
    assert dpsi_dtau == -s * psi_tau
    print("  [OK] Scale vector field d/d(ln z) on character e^{-s tau} verified")

    # 3. Hilbert-Pólya Hamiltonian eigenvalue
    # H = -i (d/dtau + 1/2)
    # H psi = -i (-s + 1/2) psi = i(s - 1/2) psi = E psi
    E = sp.Symbol("E")
    H_psi = -sp.I * (dpsi_dtau + sp.Rational(1, 2) * psi_tau)
    eigenvalue_factor = sp.simplify(H_psi / psi_tau)
    expected_E = sp.I * (s - sp.Rational(1, 2))
    assert eigenvalue_factor == expected_E

    # Two-sided inverse s(E) <-> E(s)
    def s_of_E(E_val):
        return sp.Rational(1, 2) - sp.I * E_val

    def E_of_s(s_val):
        return sp.I * (s_val - sp.Rational(1, 2))

    assert sp.simplify(E_of_s(s_of_E(E)) - E) == 0
    assert sp.simplify(s_of_E(E_of_s(s)) - s) == 0
    print("  [OK] Hilbert-Pólya affine coordinate isomorphism s(E) <-> E(s) verified")

    # 4. Spectral Reality and Critical Line
    E_re, E_im = sp.symbols("E_re E_im", real=True)
    s_complex = s_of_E(E_re + sp.I * E_im)
    s_re = sp.re(s_complex)
    # s_re is 1/2 + E_im
    assert sp.simplify(s_re - (sp.Rational(1, 2) + E_im)) == 0

    solved_E_im = sp.solve(s_re - sp.Rational(1, 2), E_im)[0]
    assert solved_E_im == 0
    print("  [OK] Im(E) = 0 <===> Re(s) = 1/2 spectral criticality verified")

    print("=" * 72)
    print("LOG-GENERATING DE RHAM PÓLYA VERIFIED")
    print("=" * 72)


if __name__ == "__main__":
    main()
