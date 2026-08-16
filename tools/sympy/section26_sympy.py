#!/usr/bin/env python3
"""Repaired Section 26: finite physical-interpretation checks.

This mirrors ``lean/InfoGeometry/Section26.lean``.  The source is mostly
physical interpretation, so the executable checks stay finite:

* complete-square algebra for the Higgs-like potential ``V(s)=-mu2*s+lam*s^2``;
* critical-value readout at ``s=mu2/(2*lam)``;
* antisymmetry and diagonal vanishing for ``F[mu,nu]=D[mu,nu]-D[nu,mu]``;
* scalar conjugacy reality readout;
* corrected quaternion gamma-bivector Hamilton table.

Not claimed: condensate existence, Lorentz breaking, emergent Maxwell
equations, gauge transformations, photons as excitations, or experimental
predictions.
"""

from __future__ import annotations

import sys
from pathlib import Path
import sympy as sp

_REPO_ROOT = Path(__file__).resolve().parents[2]
if str(_REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(_REPO_ROOT))

from tools.sympy.common import assert_matrix_zero, assert_zero


def main() -> None:
    print("=" * 72)
    print("REPAIRED SECTION 26: FINITE PHYSICAL-INTERPRETATION CORE")
    print("=" * 72)
    print("Scope: quartic algebra, Maxwell tensor shadow, scalar reality.")
    print("Open debt: condensates, gauge emergence, Maxwell dynamics, predictions.")

    mu2, lam, s = sp.symbols("mu2 lam s", nonzero=True)
    potential = -mu2 * s + lam * s**2
    critical_s = mu2 / (2 * lam)
    complete_square = lam * (s - critical_s) ** 2 - mu2**2 / (4 * lam)
    assert_zero(potential - complete_square, "quartic complete square")
    assert_zero(
        potential.subs(s, critical_s) + mu2**2 / (4 * lam),
        "quartic critical value",
    )
    print("  quartic potential complete-square identities verified")

    D = {
        (mu, nu): sp.symbols(f"D_{mu}_{nu}")
        for mu in range(4)
        for nu in range(4)
    }

    def field(mu, nu):
        return D[(mu, nu)] - D[(nu, mu)]

    for mu in range(4):
        assert_zero(field(mu, mu), "field tensor diagonal zero")
        for nu in range(4):
            assert_zero(field(nu, mu) + field(mu, nu), "field tensor antisymmetry")
    print("  finite Maxwell-style field tensor antisymmetry verified")

    ar, ai = sp.symbols("ar ai", real=True)
    A = ar + sp.I * ai
    B = sp.conjugate(A)
    readout = sp.I / 2 * (A - B)
    assert_zero(sp.im(readout), "scalar reality readout imaginary part")
    print("  scalar conjugacy reality readout verified")

    I = sp.I
    I2 = sp.eye(2)
    I4 = sp.eye(4)
    sigma1 = sp.Matrix([[0, 1], [1, 0]])
    sigma2 = sp.Matrix([[0, -I], [I, 0]])
    sigma3 = sp.Matrix([[1, 0], [0, -1]])
    tau3 = sp.Matrix([[1, 0], [0, -1]])
    epsilon = sp.Matrix([[0, 1], [-1, 0]])

    gamma0 = sp.kronecker_product(tau3, I2)
    gamma1 = sp.kronecker_product(epsilon, sigma1)
    gamma2 = sp.kronecker_product(epsilon, sigma2)
    gamma3 = sp.kronecker_product(epsilon, sigma3)
    _ = gamma0

    qi = gamma1 * gamma2
    qj = gamma2 * gamma3
    qk = gamma3 * gamma1
    assert_matrix_zero(qi * qi + I4, "qi^2 = -I")
    assert_matrix_zero(qj * qj + I4, "qj^2 = -I")
    assert_matrix_zero(qk * qk + I4, "qk^2 = -I")
    assert_matrix_zero(qi * qj - qk, "qi*qj = qk")
    assert_matrix_zero(qj * qk - qi, "qj*qk = qi")
    assert_matrix_zero(qk * qi - qj, "qk*qi = qj")
    assert_matrix_zero(qi * qj * qk + I4, "qi*qj*qk = -I")
    print("  corrected gamma-bivector Hamilton table verified")

    print("=" * 72)
    print("[SUCCESS] Section 26 theorem-safe finite checks verified.")
    print("=" * 72)


if __name__ == "__main__":
    main()
