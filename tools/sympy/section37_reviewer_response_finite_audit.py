#!/usr/bin/env python3
"""Repaired Section 37 reviewer-response finite audit.

Mirrors `InfoGeometry.Physics.Section37ReviewerResponseFiniteAudit`.
Closed finite content only:
* Tr(([H,rho]) L) = Tr(H (rho L - L rho)) for 2x2 matrices;
* finite entropy-production shadow cyclicity;
* vanishing when rho commutes with the supplied log-rho readout;
* vanishing when the two Hamiltonian components agree.

No actual entropy derivative, logarithm functional calculus, variational
Euler-Lagrange equation, Einstein/Dirac equation, Kähler integrability,
CP violation, or arrow-of-time theorem is claimed.
"""

from __future__ import annotations

import sys
from pathlib import Path
import sympy as sp

_REPO_ROOT = Path(__file__).resolve().parents[2]
if str(_REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(_REPO_ROOT))

from tools.sympy.common import assert_matrix_zero, assert_zero, comm, mat2, pauli_matrices


def entropy_von_neumann_shadow(H: sp.Matrix, rho: sp.Matrix, log_rho: sp.Matrix) -> sp.Expr:
    return sp.I * sp.trace(comm(H, rho) * log_rho)


def entropy_cyclic_shadow(H: sp.Matrix, rho: sp.Matrix, log_rho: sp.Matrix) -> sp.Expr:
    return sp.I * sp.trace(H * (rho * log_rho - log_rho * rho))


def main() -> int:
    print("=" * 72)
    print("REPAIRED SECTION 37 REVIEWER-RESPONSE FINITE AUDIT")
    print("=" * 72)

    H = mat2("H")
    rho = mat2("R")
    log_rho = mat2("L")

    assert_zero(
        sp.trace(comm(H, rho) * log_rho) - sp.trace(H * (rho * log_rho - log_rho * rho)),
        "trace commutator cyclicity",
    )
    assert_zero(
        entropy_von_neumann_shadow(H, rho, log_rho) - entropy_cyclic_shadow(H, rho, log_rho),
        "entropy shadow cyclic form",
    )
    print("finite trace/entropy cyclicity: OK")

    # Concrete commuting log-rho witness: log_rho is a polynomial in rho = diagonal.
    a, b, la, lb = sp.symbols("a b la lb")
    rho_diag = sp.diag(a, b)
    log_diag = sp.diag(la, lb)
    assert_matrix_zero(comm(rho_diag, log_diag), "rho/log-rho commuting witness")
    assert_zero(
        entropy_von_neumann_shadow(H, rho_diag, log_diag),
        "entropy shadow vanishes for commuting rho/log-rho",
    )
    print("commuting rho/log-rho zero test: OK")

    H1 = mat2("A")
    H2 = mat2("B")
    equal_subs = {
        H1[0, 0]: H2[0, 0], H1[0, 1]: H2[0, 1],
        H1[1, 0]: H2[1, 0], H1[1, 1]: H2[1, 1],
    }
    asym = H1 - H2
    assert_matrix_zero(asym.subs(equal_subs), "equal Hamiltonians zero asymmetry")
    assert_zero(
        entropy_von_neumann_shadow(asym.subs(equal_subs), rho, log_rho),
        "asymmetry entropy shadow vanishes for equal Hamiltonians",
    )
    print("Hamiltonian-asymmetry zero test: OK")

    print("=" * 72)
    print("REPAIRED SECTION 37 FINITE INTERFACE VERIFIED")
    print("=" * 72)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
