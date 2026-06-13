#!/usr/bin/env python3
"""Repaired Section 18: finite Clifford hierarchy checks.

This mirrors ``lean/InfoGeometry/Section18.lean``.

Closed finite checks:

* dimension arithmetic for the complex Clifford hierarchy:
  even levels use M_{2^k}(C), odd levels use two copies;
* the finite sequence through Cl(8,C);
* Pauli-Dirac gamma anticommutators recover the Minkowski metric readout.

Not claimed here:

* actual algebra isomorphisms for all Cl(n,C);
* tensor-product recursion as a formal construction;
* "Chirla torsion" as a theorem;
* spin statistics, CPT, gauge theory, supersymmetry, TQFT, E8, or QFT claims.
"""

from __future__ import annotations

import sympy as sp


def assert_equal(left, right, label: str) -> None:
    if sp.simplify(left - right) != 0:
        raise AssertionError(f"{label} failed: {left} != {right}")


def assert_matrix_zero(M: sp.Matrix, label: str) -> None:
    reduced = M.applyfunc(lambda x: sp.expand(sp.simplify(x)))
    if reduced != sp.zeros(*M.shape):
        raise AssertionError(f"{label} failed:\n{reduced}")


def main() -> None:
    print("=" * 72)
    print("REPAIRED SECTION 18: FINITE CLIFFORD HIERARCHY CHECKS")
    print("=" * 72)
    print("Scope: dimension arithmetic and finite gamma anticommutators.")
    print("Open debt: global Clifford isomorphisms and physics hierarchy claims.")

    for k in range(5):
        size = 2 ** k
        assert_equal(size * size, 2 ** (2 * k), f"even level k={k}")
        assert_equal(2 * size * size, 2 ** (2 * k + 1), f"odd level k={k}")
    print("  even/odd matrix dimension formulas verified through k=4")

    expected = [1, 2, 4, 8, 16, 32, 64, 128, 256]
    actual = []
    for n in range(9):
        k = n // 2
        actual.append((2 ** k) ** 2 if n % 2 == 0 else 2 * (2 ** k) ** 2)
    if actual != expected:
        raise AssertionError(f"Cl(0..8,C) dimension sequence mismatch: {actual}")
    print("  Cl(0..8,C) finite dimension sequence verified")

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
    eta = sp.diag(1, -1, -1, -1)
    for mu in range(4):
        for nu in range(4):
            anti = gammas[mu] * gammas[nu] + gammas[nu] * gammas[mu]
            assert_matrix_zero(anti - 2 * eta[mu, nu] * I4, f"gamma anticommutator {mu},{nu}")
    print("  finite gamma Jordan/metric readout verified")

    print("=" * 72)
    print("[SUCCESS] Section 18 theorem-safe finite checks verified.")
    print("=" * 72)


if __name__ == "__main__":
    main()
