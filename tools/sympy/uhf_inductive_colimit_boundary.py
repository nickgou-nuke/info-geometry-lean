"""Finite checks for the diagonal UHF/Cantor cylinder colimit.

This verifier mirrors the finite algebra promoted in
InfoGeometry.Canonical.UHFInductiveColimitBoundary:

* Kronecker tensor inclusion preserves matrix algebra operations.
* The diagonal MASA successor embedding duplicates values over the next bit.
* The diagonal embedding preserves pointwise operations and finite constants.
* Cylinder evaluation is unchanged after one successor embedding.

No C*-completion, topology, KMS state, or analytic boundary theorem is claimed.
"""

from __future__ import annotations

import sympy as sp


def kron_embed(matrix: sp.Matrix) -> sp.Matrix:
    """UHF inclusion M_n -> M_{2n}, A |-> A tensor I_2."""
    return sp.kronecker_product(matrix, sp.eye(2))


def diag_embed(values: list[sp.Expr]) -> list[sp.Expr]:
    """Diagonal successor embedding: duplicate each old cylinder value."""
    out: list[sp.Expr] = []
    for value in values:
        out.extend([value, value])
    return out


def pointwise_add(left: list[sp.Expr], right: list[sp.Expr]) -> list[sp.Expr]:
    return [a + b for a, b in zip(left, right)]


def pointwise_mul(left: list[sp.Expr], right: list[sp.Expr]) -> list[sp.Expr]:
    return [a * b for a, b in zip(left, right)]


def prefix_index(index: int) -> int:
    """For duplicated lists, the successor prefix forgets the final bit."""
    return index // 2


def cylinder(values: list[sp.Expr], boundary_index: int) -> sp.Expr:
    """Evaluate a finite cylinder observable on a finite binary prefix index."""
    return values[boundary_index]


def verify_matrix_tensor_embedding() -> None:
    a, b, c, d = sp.symbols("a b c d")
    A = sp.Matrix([[a, b], [c, d]])
    B = sp.Matrix([[1, 2], [3, 4]])

    assert kron_embed(A + B) == kron_embed(A) + kron_embed(B)
    assert kron_embed(A * B) == kron_embed(A) * kron_embed(B)
    assert kron_embed(sp.eye(2)) == sp.eye(4)


def verify_diagonal_successor_embedding() -> None:
    u0, u1, v0, v1 = sp.symbols("u0 u1 v0 v1")
    f = [u0, u1]
    g = [v0, v1]

    assert diag_embed(pointwise_add(f, g)) == pointwise_add(diag_embed(f), diag_embed(g))
    assert diag_embed(pointwise_mul(f, g)) == pointwise_mul(diag_embed(f), diag_embed(g))
    assert diag_embed([1, 1]) == [1, 1, 1, 1]
    assert diag_embed([0, 0]) == [0, 0, 0, 0]


def verify_cylinder_compatibility() -> None:
    u0, u1 = sp.symbols("u0 u1")
    f = [u0, u1]
    embedded = diag_embed(f)

    for successor_index in range(4):
        old_index = prefix_index(successor_index)
        assert cylinder(embedded, successor_index) == cylinder(f, old_index)


def verify_constant_observable_compatibility() -> None:
    z = sp.symbols("z")
    constant_stage_1 = [z, z]
    constant_stage_2 = [z, z, z, z]

    assert diag_embed(constant_stage_1) == constant_stage_2


def verify_prime_fock_constant_readout() -> None:
    x2, x3, x5 = sp.symbols("x2 x3 x5")
    graded_level_3 = sp.expand((1 - x2) * (1 - x3) * (1 - x5))
    embedded_level_3 = diag_embed([graded_level_3])

    assert embedded_level_3 == [graded_level_3, graded_level_3]


def main() -> None:
    verify_matrix_tensor_embedding()
    verify_diagonal_successor_embedding()
    verify_cylinder_compatibility()
    verify_constant_observable_compatibility()
    verify_prime_fock_constant_readout()
    print("UHF diagonal cylinder colimit finite algebra verified")


if __name__ == "__main__":
    main()
