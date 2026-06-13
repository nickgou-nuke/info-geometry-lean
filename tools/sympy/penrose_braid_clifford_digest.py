#!/usr/bin/env python3
"""
Exact finite witnesses for the Penrose / Artin braid / Clifford digest.

This script does not prove Penrose aperiodicity, configuration-space
fundamental-group theorems, or Lorentz spin geometry.  It verifies the finite
algebraic shadows that are safe to mirror in Lean:

* the 5-cycle permutation has order five;
* adjacent S3 transpositions satisfy the B3 Artin relation and square to one;
* a Hecke generator satisfies (sigma - q)(sigma + 1) = 0;
* concrete 2x2 Clifford-style generators square to +I and -I and anticommute;
* the golden ratio satisfies phi^2 = phi + 1.
"""

from __future__ import annotations

import sympy as sp


def permutation_matrix(perm: list[int]) -> sp.Matrix:
    n = len(perm)
    return sp.Matrix([[1 if perm[j] == i else 0 for j in range(n)] for i in range(n)])


def assert_matrix(name: str, lhs: sp.Matrix, rhs: sp.Matrix) -> None:
    if lhs != rhs:
        raise AssertionError(f"{name} failed:\nLHS={lhs}\nRHS={rhs}")
    print(f"PASS: {name}")


def verify_five_cycle() -> None:
    c5 = permutation_matrix([1, 2, 3, 4, 0])
    assert_matrix("5-cycle C^5 = I", c5**5, sp.eye(5))
    if c5 == sp.eye(5):
        raise AssertionError("5-cycle unexpectedly trivial")
    print("PASS: 5-cycle is nontrivial")


def verify_s3_braid_quotient() -> None:
    s1 = permutation_matrix([1, 0, 2])
    s2 = permutation_matrix([0, 2, 1])
    assert_matrix("S3 Artin relation s1 s2 s1 = s2 s1 s2", s1 * s2 * s1, s2 * s1 * s2)
    assert_matrix("S3 quotient s1^2 = I", s1**2, sp.eye(3))
    assert_matrix("S3 quotient s2^2 = I", s2**2, sp.eye(3))


def verify_hecke_relation() -> None:
    q = sp.symbols("q")
    sigma = sp.diag(q, -1)
    zero = sp.zeros(2)
    assert_matrix("Hecke quadratic (sigma - q)(sigma + 1) = 0",
                  (sigma - q * sp.eye(2)) * (sigma + sp.eye(2)), zero)


def verify_clifford_pair() -> None:
    e = sp.Matrix([[0, 1], [1, 0]])
    f = sp.Matrix([[0, 1], [-1, 0]])
    assert_matrix("Clifford e^2 = I", e * e, sp.eye(2))
    assert_matrix("Clifford f^2 = -I", f * f, -sp.eye(2))
    assert_matrix("Clifford anticommutator ef + fe = 0", e * f + f * e, sp.zeros(2))


def verify_golden_ratio() -> None:
    phi = (1 + sp.sqrt(5)) / 2
    if sp.expand(phi**2 - phi - 1) != 0:
        raise AssertionError("golden ratio relation failed")
    print("PASS: golden ratio phi^2 = phi + 1")


def main() -> None:
    print("=== Exact Penrose / Artin braid / Clifford finite digest ===")
    verify_five_cycle()
    verify_s3_braid_quotient()
    verify_hecke_relation()
    verify_clifford_pair()
    verify_golden_ratio()
    print("All exact SymPy digest checks passed.")


if __name__ == "__main__":
    main()
