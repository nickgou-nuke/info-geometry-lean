#!/usr/bin/env python3
"""Repaired Section 31 finite unified-matrix dynamics layer.

Uses the already-formalized finite Pauli/Bloch matrix framework as a stepping
stone and checks only algebraic identities:
- von-Neumann commutator equals Bloch precession (already mirrored earlier);
- constant covariant derivatives D_Gamma X=[Gamma,X] satisfy
  [D_Gamma,D_Lambda]X = [[Gamma,Lambda],X];
- zero connection has zero curvature/action;
- constant gauge conjugation covariance with an explicit inverse.

No smooth gauge bundle, local SU(2) connection theorem, Einstein-equation
result, gravity-from-entanglement theorem, or spacetime emergence theorem is
asserted.
"""

import sys
from pathlib import Path
import sympy as sp

_REPO_ROOT = Path(__file__).resolve().parents[2]
if str(_REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(_REPO_ROOT))

from tools.sympy.common import assert_matrix_zero, comm, mat2, pauli_matrices


def main() -> None:
    print("=== Repaired Section 31 finite unified-matrix dynamics ===")

    I = sp.I
    sigma1 = sp.Matrix([[0, 1], [1, 0]])
    sigma2 = sp.Matrix([[0, -I], [I, 0]])
    sigma3 = sp.Matrix([[1, 0], [0, -1]])

    w1, w2, w3, n1, n2, n3 = sp.symbols("w1 w2 w3 n1 n2 n3")
    rho = sp.Matrix([[(1 + n3) / 2, (n1 - I * n2) / 2], [(n1 + I * n2) / 2, (1 - n3) / 2]])
    H = sp.Matrix([[w3 / 2, (w1 - I * w2) / 2], [(w1 + I * w2) / 2, -w3 / 2]])
    rhs = -I * comm(H, rho)
    cross = ((w2*n3 - w3*n2)*sigma1 + (w3*n1 - w1*n3)*sigma2 + (w1*n2 - w2*n1)*sigma3) / 2
    assert_matrix_zero(rhs - cross, "finite Bloch precession commutator")
    print("Bloch precession commutator: OK")

    G = mat2("G")
    L = mat2("L")
    X = mat2("X")
    curvature_action = comm(G, comm(L, X)) - comm(L, comm(G, X)) - comm(comm(G, L), X)
    assert_matrix_zero(curvature_action, "constant curvature/Jacobi action")
    print("[D_G,D_L]X = [[G,L],X]: OK")

    Z = sp.zeros(2)
    assert_matrix_zero(comm(Z, G), "zero curvature left")
    assert_matrix_zero(comm(Z, X), "zero covariant derivative")
    print("zero connection identities: OK")

    # Concrete invertible/gauge witness: diagonal U and V=U^{-1}.
    a, b = sp.symbols("a b", nonzero=True)
    U = sp.diag(a, b)
    V = sp.diag(1/a, 1/b)
    conjugation_gap = comm(U*G*V, U*X*V) - U*comm(G, X)*V
    assert_matrix_zero(conjugation_gap, "constant conjugation covariance")
    print("constant gauge conjugation covariance: OK")

    print("[SUCCESS] repaired finite Section 31 dynamics identities verified.")


if __name__ == "__main__":
    main()
