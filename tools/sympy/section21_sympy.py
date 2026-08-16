#!/usr/bin/env python3
"""Repaired Section 21: finite spinor-condensate algebra checks.

This mirrors ``lean/InfoGeometry/Section21.lean``.

Closed finite checks:

* the Pauli-Dirac projector P = 1/4 (1 + gamma0)(1 + i gamma1 gamma2) is
  idempotent;
* the induced metric readout eta_ab e^a_mu e^b_nu is symmetric;
* sigma_{mu,nu} = 1/2 [gamma_mu, gamma_nu] is antisymmetric;
* adding zero contorsion to a finite spin connection changes nothing.

Not claimed here:

* condensate existence or vacuum expectation values;
* minimal-left-ideal classification;
* Einstein-Cartan field equations;
* effective action variation or stress-energy derivation.
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
    print("REPAIRED SECTION 21: FINITE SPINOR-CONDENSATE ALGEBRA")
    print("=" * 72)
    print("Scope: projector, metric readout, gamma commutator, contorsion split.")
    print("Open debt: condensate dynamics, actions, stress-energy, field equations.")

    I = sp.I
    I2 = sp.eye(2)
    I4 = sp.eye(4)
    sigma1 = sp.Matrix([[0, 1], [1, 0]])
    sigma2 = sp.Matrix([[0, -I], [I, 0]])
    sigma3 = sp.Matrix([[1, 0], [0, -1]])
    tau3 = sp.Matrix([[1, 0], [0, -1]])
    epsilon = sp.Matrix([[0, 1], [-1, 0]])
    gammas = [
        sp.kronecker_product(tau3, I2),
        sp.kronecker_product(epsilon, sigma1),
        sp.kronecker_product(epsilon, sigma2),
        sp.kronecker_product(epsilon, sigma3),
    ]

    projector = sp.Rational(1, 4) * (I4 + gammas[0]) * (I4 + I * gammas[1] * gammas[2])
    assert_matrix_zero(projector * projector - projector, "spinor projector idempotent")
    print("  Pauli-Dirac projector idempotence verified")

    e = {
        (a, mu): sp.symbols(f"e_{a}_{mu}")
        for a in range(4)
        for mu in range(4)
    }

    def induced_metric(mu, nu):
        return (
            e[(0, mu)] * e[(0, nu)]
            - e[(1, mu)] * e[(1, nu)]
            - e[(2, mu)] * e[(2, nu)]
            - e[(3, mu)] * e[(3, nu)]
        )

    for mu in range(4):
        for nu in range(4):
            assert_zero(induced_metric(mu, nu) - induced_metric(nu, mu), "induced metric symmetry")
    print("  finite induced metric symmetry verified")

    def gamma_sigma(mu, nu):
        return sp.Rational(1, 2) * (gammas[mu] * gammas[nu] - gammas[nu] * gammas[mu])

    for mu in range(4):
        for nu in range(4):
            assert_matrix_zero(gamma_sigma(nu, mu) + gamma_sigma(mu, nu), "gamma sigma antisymmetry")
    print("  gamma commutator bivector antisymmetry verified")

    lc00, lc01, lc10, lc11 = sp.symbols("lc00 lc01 lc10 lc11")
    omega_lc = sp.Matrix([[lc00, lc01], [lc10, lc11]])
    contorsion_zero = sp.zeros(2)
    if omega_lc + contorsion_zero != omega_lc:
        raise AssertionError("zero contorsion should recover Levi-Civita spin connection")
    print("  zero-contorsion connection split verified")

    print("=" * 72)
    print("[SUCCESS] Section 21 theorem-safe finite checks verified.")
    print("=" * 72)


if __name__ == "__main__":
    main()
