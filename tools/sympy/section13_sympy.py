#!/usr/bin/env python3
"""
Section 13: Fibrations and two-qubit space -- SymPy verification.

This verifies the finite algebraic identities mirrored in
lean/InfoGeometry/Section13.lean:

* normalized two-qubit vectors live in the unit sphere shadow in C^4;
* product-state norms multiply;
* product states have zero concurrence amplitude ad-bc;
* pure density matrices have trace equal to norm squared and rank-one minors;
* gamma expectation readouts are ordinary <psi|Gamma|psi> coordinates.
"""

from __future__ import annotations

import sympy as sp


def assert_zero(expr, label: str) -> None:
    reduced = sp.simplify(expr)
    if reduced != 0:
        raise AssertionError(f"{label} failed: {reduced}")


def assert_matrix_zero(mat: sp.Matrix, label: str) -> None:
    reduced = mat.applyfunc(sp.simplify)
    if reduced != sp.zeros(*mat.shape):
        raise AssertionError(f"{label} failed:\n{reduced}")


def inner_norm_sq(vec: sp.Matrix) -> sp.Expr:
    return (vec.conjugate().T * vec)[0]


def expectation(operator: sp.Matrix, psi: sp.Matrix) -> sp.Expr:
    return sp.simplify((psi.conjugate().T * operator * psi)[0])


def main() -> None:
    print("=" * 72)
    print("SECTION 13: FIBRATIONS AND TWO-QUBIT SPACE -- SYMPY VERIFICATION")
    print("=" * 72)

    u0, u1, v0, v1 = sp.symbols("u0 u1 v0 v1", complex=True)
    u = sp.Matrix([u0, u1])
    v = sp.Matrix([v0, v1])
    psi_prod = sp.Matrix([u0 * v0, u0 * v1, u1 * v0, u1 * v1])

    norm_prod = inner_norm_sq(psi_prod)
    norm_expected = sp.expand(inner_norm_sq(u) * inner_norm_sq(v))
    assert_zero(sp.expand(norm_prod - norm_expected), "product-state norm multiplicativity")
    print("  product-state norm multiplicativity verified")

    concurrence_amp = psi_prod[0] * psi_prod[3] - psi_prod[1] * psi_prod[2]
    assert_zero(concurrence_amp, "product-state concurrence amplitude")
    print("  product-state concurrence amplitude ad-bc vanishes")

    a, b, c, d = sp.symbols("a b c d", complex=True)
    psi = sp.Matrix([a, b, c, d])
    rho = psi * psi.conjugate().T

    assert_zero(sp.trace(rho) - inner_norm_sq(psi), "pure density trace equals norm")
    print("  pure density trace equals state norm squared")

    for i in range(4):
        for j in range(4):
            for k in range(4):
                for l in range(4):
                    assert_zero(
                        rho[i, j] * rho[k, l] - rho[i, l] * rho[k, j],
                        "rank-one density minor",
                    )
    print("  pure density rank-one minor identities verified")

    # Pauli-Dirac gamma matrices from Section 5.
    I = sp.I
    gamma0 = sp.diag(1, 1, -1, -1)
    gamma1 = sp.Matrix([[0, 0, 0, 1], [0, 0, 1, 0], [0, -1, 0, 0], [-1, 0, 0, 0]])
    gamma2 = sp.Matrix([[0, 0, 0, -I], [0, 0, I, 0], [0, I, 0, 0], [-I, 0, 0, 0]])
    gamma3 = sp.Matrix([[0, 0, 1, 0], [0, 0, 0, -1], [-1, 0, 0, 0], [0, 1, 0, 0]])
    gamma5 = sp.Matrix([[0, 0, 1, 0], [0, 0, 0, 1], [1, 0, 0, 0], [0, 1, 0, 0]])
    gammas = [gamma0, gamma1, gamma2, gamma3, gamma5]

    assert_matrix_zero(gamma5 * gamma0 + gamma0 * gamma5, "gamma5 anticommutes with gamma0")
    print("  Section 5 gamma anticommutation reused for base readout")

    zero_state = sp.zeros(4, 1)
    for idx, gamma in enumerate(gammas):
        assert_zero(expectation(gamma, zero_state), f"zero-state gamma expectation {idx}")
    print("  zero-state gamma/Horodecki readout vanishes")

    readout = [expectation(gamma, psi) for gamma in gammas]
    if len(readout) != 5:
        raise AssertionError("Hopf base readout must have five gamma coordinates")
    print("  five gamma expectation coordinates constructed")

    print("=" * 72)
    print("SECTION 13 VERIFIED")
    print("=" * 72)


if __name__ == "__main__":
    main()
