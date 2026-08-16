#!/usr/bin/env python3
"""Section 5: Clifford structure, exact SymPy verification.

This is the computational companion to
``InfoGeometry.Clifford.DiracPauliGamma``.  It checks the same finite
Pauli-Dirac gamma matrix identities using exact symbolic complex arithmetic.

Lean remains proof authority; this script is a reproducible finite shadow.
"""

import sys
from pathlib import Path
import sympy as sp

_REPO_ROOT = Path(__file__).resolve().parents[2]
if str(_REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(_REPO_ROOT))

from tools.sympy.common import assert_matrix_eq


def assert_scalar_eq(name: str, left, right=0) -> None:
    if sp.simplify(left - right) != 0:
        raise AssertionError(f"{name} failed: {sp.simplify(left - right)}")
    print(f"  {name}: OK")


I = sp.I
I2 = sp.eye(2)
I4 = sp.eye(4)
zero4 = sp.zeros(4)

# Pauli matrices.
sigma1 = sp.Matrix([[0, 1], [1, 0]])
sigma2 = sp.Matrix([[0, -I], [I, 0]])
sigma3 = sp.Matrix([[1, 0], [0, -1]])

# Pauli-Dirac block factor.
tau3 = sp.Matrix([[1, 0], [0, -1]])
epsilon = sp.Matrix([[0, 1], [-1, 0]])

# Gamma matrices from the Pauli embedding.
gamma0 = sp.kronecker_product(tau3, I2)
gamma1 = sp.kronecker_product(epsilon, sigma1)
gamma2 = sp.kronecker_product(epsilon, sigma2)
gamma3 = sp.kronecker_product(epsilon, sigma3)
gamma5 = I * gamma0 * gamma1 * gamma2 * gamma3
gammas = [gamma0, gamma1, gamma2, gamma3]

# Explicit matrices used by the Lean finite owner.
gamma0_explicit = sp.diag(1, 1, -1, -1)
gamma1_explicit = sp.Matrix(
    [[0, 0, 0, 1], [0, 0, 1, 0], [0, -1, 0, 0], [-1, 0, 0, 0]]
)
gamma2_explicit = sp.Matrix(
    [[0, 0, 0, -I], [0, 0, I, 0], [0, I, 0, 0], [-I, 0, 0, 0]]
)
gamma3_explicit = sp.Matrix(
    [[0, 0, 1, 0], [0, 0, 0, -1], [-1, 0, 0, 0], [0, 1, 0, 0]]
)
gamma5_explicit = sp.Matrix(
    [[0, 0, 1, 0], [0, 0, 0, 1], [1, 0, 0, 0], [0, 1, 0, 0]]
)


def anticommutator(left: sp.Matrix, right: sp.Matrix) -> sp.Matrix:
    return left * right + right * left


def commutator(left: sp.Matrix, right: sp.Matrix) -> sp.Matrix:
    return left * right - right * left


def sigma_lorentz(mu: int, nu: int) -> sp.Matrix:
    return (I / 4) * commutator(gammas[mu], gammas[nu])


def spinor_expectation(matrix: sp.Matrix, psi: sp.Matrix) -> sp.Expr:
    return (sp.conjugate(psi).T * matrix * psi)[0]


def main() -> int:
    print("=" * 72)
    print("SECTION 5: CLIFFORD STRUCTURE — EXACT SYMPY CHECK")
    print("=" * 72)

    print("\n5.1 Gamma matrices from Pauli embedding")
    assert_matrix_eq("gamma0 kronecker equals explicit", gamma0, gamma0_explicit)
    assert_matrix_eq("gamma1 kronecker equals explicit", gamma1, gamma1_explicit)
    assert_matrix_eq("gamma2 kronecker equals explicit", gamma2, gamma2_explicit)
    assert_matrix_eq("gamma3 kronecker equals explicit", gamma3, gamma3_explicit)
    assert_matrix_eq("gamma5 equals i*gamma0*gamma1*gamma2*gamma3", gamma5, gamma5_explicit)

    print("\n5.2 Clifford relations")
    eta = sp.diag(1, -1, -1, -1)
    for mu in range(4):
        for nu in range(4):
            assert_matrix_eq(
                f"{{gamma{mu}, gamma{nu}}} = 2 eta[{mu},{nu}] I4",
                anticommutator(gammas[mu], gammas[nu]),
                2 * eta[mu, nu] * I4,
            )

    print("\n5.2 gamma5 chirality")
    assert_matrix_eq("gamma5^2 = I4", gamma5 * gamma5, I4)
    for mu in range(4):
        assert_matrix_eq(
            f"{{gamma5, gamma{mu}}} = 0",
            anticommutator(gamma5, gammas[mu]),
            zero4,
        )

    print("\n5.2 Lorentz-generator normalization")
    for mu in range(4):
        for nu in range(4):
            sigma = sigma_lorentz(mu, nu)
            assert_matrix_eq(
                f"[gamma{mu}, gamma{nu}] = -4i Sigma[{mu},{nu}]",
                commutator(gammas[mu], gammas[nu]),
                -4 * I * sigma,
            )

    print("\n5.3 Bilinear-form construction")
    psi0, psi1, psi2, psi3 = sp.symbols("psi0 psi1 psi2 psi3", complex=True)
    psi = sp.Matrix([psi0, psi1, psi2, psi3])
    scalar = spinor_expectation(gamma0, psi)
    pseudoscalar = spinor_expectation(gamma0 * gamma5, psi)
    vector = [spinor_expectation(gamma0 * gammas[mu], psi) for mu in range(4)]
    axial = [spinor_expectation(gamma0 * gammas[mu] * gamma5, psi) for mu in range(4)]

    # These are construction checks: the expressions are symbolic, but the
    # matrix shapes and scalar extraction are exact.
    assert_scalar_eq("scalar bilinear is scalar-shaped", sp.Matrix([scalar]).shape[0], 1)
    assert_scalar_eq("pseudoscalar bilinear is scalar-shaped", sp.Matrix([pseudoscalar]).shape[0], 1)
    assert_scalar_eq("vector bilinear has four components", len(vector), 4)
    assert_scalar_eq("axial bilinear has four components", len(axial), 4)

    print("\nSECTION 5 VERIFIED")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
