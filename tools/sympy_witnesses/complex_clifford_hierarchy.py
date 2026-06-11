#!/usr/bin/env python3
"""Finite matrix witnesses for the complex Clifford hierarchy.

This script verifies the concrete Pauli/Kronecker model, not an abstract
classification theorem.  Odd complex Clifford algebras are represented by the
faithful two-block split, matching Cl(2k+1,C) = M_{2^k}(C) ⊕ M_{2^k}(C).
"""

from __future__ import annotations

import itertools
import sympy as sp


I = sp.I

SIGMA_1 = sp.Matrix([[0, 1], [1, 0]])
SIGMA_2 = sp.Matrix([[0, -I], [I, 0]])
SIGMA_3 = sp.Matrix([[1, 0], [0, -1]])


def matrix_equal(a: sp.Matrix, b: sp.Matrix) -> bool:
    return all(sp.simplify(x) == 0 for x in list(a - b))


def block_diag(a: sp.Matrix, b: sp.Matrix) -> sp.Matrix:
    return sp.diag(a, b)


def even_generators(k: int) -> list[sp.Matrix]:
    """Generators for a matrix model of Cl(2k,C), with e_i^2 = +1."""
    if k == 0:
        return []

    previous = even_generators(k - 1)
    previous_size = 2 ** (k - 1)
    previous_id = sp.eye(previous_size)

    lifted = [sp.kronecker_product(g, SIGMA_3) for g in previous]
    new_pair = [
        sp.kronecker_product(previous_id, SIGMA_1),
        sp.kronecker_product(previous_id, SIGMA_2),
    ]
    return lifted + new_pair


def normalized_volume(gens: list[sp.Matrix]) -> sp.Matrix:
    size = gens[0].rows if gens else 1
    volume = sp.eye(size)
    for g in gens:
        volume = volume * g

    volume_sq = sp.simplify(volume * volume)
    identity = sp.eye(size)
    if matrix_equal(volume_sq, identity):
        return volume
    if matrix_equal(volume_sq, -identity):
        return I * volume
    raise AssertionError("volume element does not square to +/- identity")


def odd_generators(k: int) -> list[sp.Matrix]:
    """Faithful two-block generators for Cl(2k+1,C)."""
    if k == 0:
        return [sp.diag(1, -1)]

    even = even_generators(k)
    chirality = normalized_volume(even)
    lifted = [block_diag(g, g) for g in even]
    return lifted + [block_diag(chirality, -chirality)]


def clifford_generators(n: int) -> list[sp.Matrix]:
    if n % 2 == 0:
        return even_generators(n // 2)
    return odd_generators(n // 2)


def monomial_basis(gens: list[sp.Matrix]) -> list[sp.Matrix]:
    size = gens[0].rows if gens else 1
    basis = []
    for mask in range(1 << len(gens)):
        m = sp.eye(size)
        for i, g in enumerate(gens):
            if mask & (1 << i):
                m = m * g
        basis.append(m)
    return basis


def span_rank(matrices: list[sp.Matrix]) -> int:
    columns = []
    for m in matrices:
        columns.append(sp.Matrix(m.rows * m.cols, 1, list(m)))
    return sp.Matrix.hstack(*columns).rank()


def verify_clifford_relations(gens: list[sp.Matrix]) -> None:
    if not gens:
        return
    size = gens[0].rows
    identity = sp.eye(size)
    zero = sp.zeros(size)
    for i, j in itertools.product(range(len(gens)), repeat=2):
        anticomm = gens[i] * gens[j] + gens[j] * gens[i]
        expected = 2 * identity if i == j else zero
        if not matrix_equal(anticomm, expected):
            raise AssertionError(f"Clifford relation failed for ({i}, {j})")


def verify_odd_projectors(gens: list[sp.Matrix]) -> None:
    volume = normalized_volume(gens)
    size = volume.rows
    identity = sp.eye(size)

    for g in gens:
        if not matrix_equal(volume * g, g * volume):
            raise AssertionError("odd volume element is not central")

    p_plus = (identity + volume) / 2
    p_minus = (identity - volume) / 2
    checks = [
        matrix_equal(p_plus * p_plus, p_plus),
        matrix_equal(p_minus * p_minus, p_minus),
        matrix_equal(p_plus * p_minus, sp.zeros(size)),
        matrix_equal(p_plus + p_minus, identity),
    ]
    if not all(checks):
        raise AssertionError("central projectors failed")


def shape_label(n: int) -> str:
    k = n // 2
    block = 2**k
    if n % 2 == 0:
        return f"M_{block}(C)"
    return f"M_{block}(C) + M_{block}(C)"


def expected_complex_dimension(n: int) -> int:
    return 2**n


def run() -> None:
    print("Complex Clifford hierarchy witness, convention e_i^2 = +1")
    print("n | shape                  | matrix size | span rank | expected dim")
    print("--+------------------------+-------------+-----------+-------------")

    for n in range(0, 9):
        gens = clifford_generators(n)
        verify_clifford_relations(gens)
        if n % 2 == 1:
            verify_odd_projectors(gens)

        basis = monomial_basis(gens)
        rank = span_rank(basis)
        expected = expected_complex_dimension(n)
        size = basis[0].rows
        if rank != expected:
            raise AssertionError(f"basis rank mismatch for Cl({n},C): {rank} != {expected}")

        print(f"{n:1d} | {shape_label(n):22s} | {size:>4d}x{size:<4d} | {rank:>9d} | {expected:>11d}")

    print("OK: Pauli/Kronecker generators realize the finite hierarchy through Cl(8,C).")


if __name__ == "__main__":
    run()
