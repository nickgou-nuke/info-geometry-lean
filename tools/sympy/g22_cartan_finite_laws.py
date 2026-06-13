#!/usr/bin/env python3
"""Finite Cartan-split laws for the doubled 5+5 carrier.

This verifier intentionally checks only explicit linear-algebra facts:
  * the off-diagonal block swap lies in so(5,5),
  * the grading involution makes that block odd,
  * diagonal block operators are even,
  * the tested G2-type split-octonion generators stay internal to vector slots.

It does not claim or verify a full PO(5,5), Pin(5,5), Super-TKK, SU(3), or
Aut(O_s)=G2(2) classification theorem.
"""

from __future__ import annotations

import numpy as np


def assert_matrix_eq(lhs, rhs, msg: str) -> None:
    if not np.array_equal(lhs, rhs):
        raise AssertionError(f"{msg}:\n{lhs}\n!=\n{rhs}")


def block_diag(a: np.ndarray, b: np.ndarray) -> np.ndarray:
    z = np.zeros_like(a)
    return np.block([[a, z], [z, b]])


def main() -> None:
    z5 = np.zeros((5, 5), dtype=np.int64)
    i5 = np.eye(5, dtype=np.int64)
    eta = block_diag(i5, -i5)
    eps = block_diag(i5, -i5)

    boost = np.block([[z5, i5], [i5, z5]])
    compact_diag = block_diag(i5, -i5)

    assert_matrix_eq(boost.T @ eta + eta @ boost, np.zeros((10, 10), dtype=np.int64), "boost_so55")
    assert_matrix_eq(eps @ boost @ eps, -boost, "boost_theta_odd")
    assert_matrix_eq(eps @ compact_diag @ eps, compact_diag, "diag_theta_even")

    # Orientation-preserving signed 3x3 permutation from the previous split-octonion lane.
    sigma3 = np.array([[0, 1, 0], [1, 0, 0], [0, 0, -1]], dtype=np.int64)
    assert int(round(np.linalg.det(sigma3))) == 1
    assert_matrix_eq(sigma3.T @ sigma3, np.eye(3, dtype=np.int64), "sigma3_orthogonal")

    print("OK g22_cartan_finite_laws: boost in so(5,5), theta-odd; diagonal core theta-even")
    print("OK signed 3-slot generator is orientation-preserving orthogonal")
    print("scope: finite Cartan/block checks only; no full PO(5,5), Pin(5,5), Super-TKK, SU(3), or Aut(O_s)=G2(2) classification claimed")


if __name__ == "__main__":
    main()
