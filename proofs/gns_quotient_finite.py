#!/usr/bin/env python3
"""
Finite GNS quotient witness for the vector state on M_2(C).

The GNS relation identifies matrices with the same first column, i.e. matrices
that act identically on Ω=e0.  The quotient inner product is
    <[A],[B]> = ω(A†B),   ω(A)=<Ω,AΩ>=A_00.
This script checks well-definedness, representation by left multiplication, the
expectation identity, cyclicity, and non-faithfulness of the vector state.
"""

from __future__ import annotations

import sympy as sp


def dagger(A: sp.Matrix) -> sp.Matrix:
    return A.conjugate().T


def omega(A: sp.Matrix) -> sp.Expr:
    return A[0, 0]


def inner_raw(A: sp.Matrix, B: sp.Matrix) -> sp.Expr:
    return sp.simplify(omega(dagger(A) * B))


def same_gns_class(A: sp.Matrix, B: sp.Matrix) -> bool:
    return sp.simplify(A[0, 0] - B[0, 0]) == 0 and sp.simplify(A[1, 0] - B[1, 0]) == 0


def main() -> None:
    a00, a01, a10, a11 = sp.symbols("a00 a01 a10 a11")
    b00, b01, b10, b11 = sp.symbols("b00 b01 b10 b11")
    c01, c11 = sp.symbols("c01 c11")
    d01, d11 = sp.symbols("d01 d11")

    A = sp.Matrix([[a00, a01], [a10, a11]])
    B = sp.Matrix([[b00, b01], [b10, b11]])

    # Equivalent representatives differ only in their second column.
    Aprime = sp.Matrix([[a00, c01], [a10, c11]])
    Bprime = sp.Matrix([[b00, d01], [b10, d11]])
    assert same_gns_class(A, Aprime)
    assert same_gns_class(B, Bprime)

    # Inner product depends only on first columns.
    assert sp.simplify(inner_raw(A, B) - (sp.conjugate(a00) * b00 + sp.conjugate(a10) * b10)) == 0
    assert sp.simplify(inner_raw(A, B) - inner_raw(Aprime, Bprime)) == 0

    # Representation is left multiplication and is well-defined on classes.
    x00, x01, x10, x11 = sp.symbols("x00 x01 x10 x11")
    X = sp.Matrix([[x00, x01], [x10, x11]])
    Xprime = sp.Matrix([[x00, c01], [x10, c11]])
    assert same_gns_class(X, Xprime)
    assert same_gns_class(A * X, A * Xprime)

    # Multiplication representation π(A)π(B)=π(AB) on GNS classes.
    assert same_gns_class((A * B) * X, A * (B * X))

    # Expectation identity: <[1], π(A)[1]> = omega(A).
    Id = sp.eye(2)
    assert sp.simplify(inner_raw(Id, A * Id) - omega(A)) == 0

    # Cyclicity: any class [X] = π(X)[1].
    assert same_gns_class(X * Id, X)

    # Nonfaithfulness: a nonzero operator with zero first column becomes null.
    null_example = sp.Matrix([[0, 1], [0, 0]])
    assert same_gns_class(null_example, sp.zeros(2))
    assert null_example != sp.zeros(2)

    print("gns_quotient_finite.py: exact finite GNS quotient witnesses passed")
    print("  GNS relation = same first column = same action on Ω")
    print("  inner product well-defined on quotient")
    print("  π(A)[X]=[AX] well-defined and multiplicative")
    print("  ω(A)=<[1],π(A)[1]> verified")
    print("  vector-state GNS quotient is cyclic but not faithful")


if __name__ == "__main__":
    main()
