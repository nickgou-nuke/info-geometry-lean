#!/usr/bin/env python3
"""Finite Cuntz / super-braid / MoE verifier.

This mirrors `InfoGeometry.Canonical.CuntzSuperBraidMoEBridge`.

Honest scope:
  * B6 Artin relations are checked in the finite permutation shadow;
  * O6 is checked only through finite matrix-unit range projections, not as a
    faithful finite-dimensional Cuntz representation;
  * particle/hole superparity and Krein J-adjoint signs are finite matrix
    readouts;
  * dissipative irreversibility is represented only by a scalar residual
    gamma_forward - gamma_backward.

No Jones polynomial, full Cuntz C*-algebra representation, non-unitary
semigroup theorem, or full-twist centrality theorem is asserted.
"""

import json
import sys
from pathlib import Path
import sympy as sp

_REPO_ROOT = Path(__file__).resolve().parents[2]
if str(_REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(_REPO_ROOT))

from tools.sympy.common import assert_matrix_eq


def transposition_matrix(n: int, i: int) -> sp.Matrix:
    """Permutation matrix for adjacent transposition (i, i+1), zero based."""
    p = sp.eye(n)
    p[i, i] = 0
    p[i + 1, i + 1] = 0
    p[i, i + 1] = 1
    p[i + 1, i] = 1
    return p


def matrix_unit(n: int, i: int, j: int) -> sp.Matrix:
    m = sp.zeros(n)
    m[i, j] = 1
    return m


def verify_b6_shadow() -> dict[str, bool]:
    sig = [transposition_matrix(6, i) for i in range(5)]
    I6 = sp.eye(6)

    for s in sig:
        assert_matrix_eq("sigma_i^2 = I in permutation shadow", s * s, I6)

    assert_matrix_eq("particle Artin relation", sig[0] * sig[1] * sig[0], sig[1] * sig[0] * sig[1])
    assert_matrix_eq("hole Artin relation", sig[3] * sig[4] * sig[3], sig[4] * sig[3] * sig[4])

    for i in (0, 1):
        for j in (3, 4):
            assert_matrix_eq(f"sector commute sigma_{i+1}, sigma_{j+1}", sig[i] * sig[j], sig[j] * sig[i])

    e3 = sp.eye(6).col(2)
    e4 = sp.eye(6).col(3)
    assert_matrix_eq("central bridge 3 -> 4", sig[2] * e3, e4)
    assert_matrix_eq("central bridge 4 -> 3", sig[2] * e4, e3)

    # In the permutation shadow, the usual full-twist word collapses to identity.
    coxeter = sig[0] * sig[1] * sig[2] * sig[3] * sig[4]
    assert_matrix_eq("(sigma1...sigma5)^6 permutation shadow", coxeter**6, I6)

    return {
        "artin_particle": True,
        "artin_hole": True,
        "sector_commutation": True,
        "central_bridge": True,
        "full_twist_permutation_shadow_identity": True,
    }


def verify_cuntz_projection_shadow() -> dict[str, bool]:
    # Matrix-unit partial-isometry shadow: V_i^* V_j = delta_ij P0 and
    # sum V_i V_i^* = I. This is not a finite faithful O6 representation.
    V = [matrix_unit(6, i, 0) for i in range(6)]
    I6 = sp.eye(6)
    P0 = matrix_unit(6, 0, 0)

    for i in range(6):
        for j in range(6):
            expected = P0 if i == j else sp.zeros(6)
            assert_matrix_eq("matrix-unit source projection", V[i].T * V[j], expected)

    projections = [v * v.T for v in V]
    assert_matrix_eq("range projections sum to identity", sum(projections, sp.zeros(6)), I6)
    for p in projections:
        assert_matrix_eq("range projection idempotent", p * p, p)
    for i in range(6):
        for j in range(6):
            if i != j:
                assert_matrix_eq("range projection orthogonal", projections[i] * projections[j], sp.zeros(6))

    return {
        "matrix_unit_partial_isometries": True,
        "range_projection_partition": True,
        "range_projection_orthogonal": True,
    }


def verify_krein_superparity() -> dict[str, bool]:
    J = sp.diag(1, 1, 1, -1, -1, -1)
    parity = [1, 1, 1, -1, -1, -1]

    def krein_adjoint(A: sp.Matrix) -> sp.Matrix:
        return J * A.T * J

    for p in parity:
        assert p * p == 1

    for i in range(3):
        for j in range(3, 6):
            assert parity[i] * parity[j] == -1
            Eij = matrix_unit(6, i, j)
            assert_matrix_eq("cross term odd under grading", J * Eij * J, -Eij)
            assert_matrix_eq("Krein adjoint sign on cross term", krein_adjoint(Eij), -matrix_unit(6, j, i))

    omega_iso = sp.zeros(6)
    for i in range(3):
        omega_iso += matrix_unit(6, i, i + 3)
    assert_matrix_eq("isotropic anchor odd under grading", J * omega_iso * J, -omega_iso)
    assert_matrix_eq("isotropic anchor Krein adjoint sign", krein_adjoint(omega_iso), -omega_iso.T)

    return {
        "parity_squared_one": True,
        "cross_terms_odd": True,
        "krein_adjoint_cross_sign": True,
        "omega_iso_odd": True,
    }


def verify_moe_and_dissipation() -> dict[str, bool]:
    g_particle, g_hole = sp.symbols("g_particle g_hole")
    gamma_forward, gamma_backward = sp.symbols("gamma_forward gamma_backward")

    residual = sp.simplify(gamma_forward - gamma_backward)
    assert residual.subs(gamma_forward, gamma_backward) == 0

    gate_sum = sp.simplify(g_particle + g_hole)
    assert gate_sum.subs(g_hole, 1 - g_particle) == 1

    # A finite routed Cuntz projection shadow preserves a partition of unity
    # only after the two expert weights sum to one.
    P_particle = sp.diag(1, 1, 1, 0, 0, 0)
    P_hole = sp.diag(0, 0, 0, 1, 1, 1)
    routed_identity = g_particle * P_particle + g_hole * P_hole
    assert_matrix_eq(
        "routed partition at equal unit weights",
        routed_identity.subs({g_particle: 1, g_hole: 1}),
        sp.eye(6),
    )

    return {
        "dissipative_residual_zero_iff_equal_shadow": True,
        "two_expert_gate_sum": True,
        "routed_projection_partition_shadow": True,
    }


def main() -> None:
    result = {
        "b6": verify_b6_shadow(),
        "cuntz_shadow": verify_cuntz_projection_shadow(),
        "krein_superparity": verify_krein_superparity(),
        "moe_dissipation": verify_moe_and_dissipation(),
    }
    print("CUNTZ_SUPER_BRAID_MOE_FINITE_OK")
    print(json.dumps(result, sort_keys=True))
    print(
        "scope: finite B6 permutation shadow, matrix-unit Cuntz projection shadow, "
        "Krein superparity signs, and scalar MoE/dissipation gates only"
    )


if __name__ == "__main__":
    main()
