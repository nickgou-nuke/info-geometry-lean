#!/usr/bin/env python3
"""Common SymPy helpers for `formal-theory-quantum.lean` companions.

These scripts are computational shadows for chapter stubs.  They compute and
check explicit polynomial identities, while Lean remains the proof authority.
"""

from __future__ import annotations

import sympy as sp


def mat_eq(left: sp.MatrixBase, right: sp.MatrixBase) -> bool:
    diff = sp.Matrix(left) - sp.Matrix(right)
    diff = diff.applyfunc(sp.simplify)
    return diff == sp.zeros(diff.rows, diff.cols)


def scalar_eq(left, right=0) -> bool:
    return sp.simplify(left - right) == 0


def check(name: str, condition: bool) -> None:
    if not condition:
        raise AssertionError(name)
    print(f"  {name}: OK")


def kron(left: sp.MatrixBase, right: sp.MatrixBase) -> sp.Matrix:
    return sp.kronecker_product(left, right)


def swap_2_tensor() -> sp.Matrix:
    return sp.Matrix(
        [
            [1, 0, 0, 0],
            [0, 0, 1, 0],
            [0, 1, 0, 0],
            [0, 0, 0, 1],
        ]
    )


def fundamental_uqsl2(q) -> tuple[sp.Matrix, sp.Matrix, sp.Matrix, sp.Matrix]:
    E = sp.Matrix([[0, 1], [0, 0]])
    F = sp.Matrix([[0, 0], [1, 0]])
    K = sp.diag(q, q**-1)
    return E, F, K, K.inv()


def universal_R_fundamental(q) -> sp.Matrix:
    return sp.Matrix(
        [
            [q, 0, 0, 0],
            [0, 1, 0, 0],
            [0, q - q**-1, 1, 0],
            [0, 0, 0, q],
        ]
    )


def braid_Rcheck_fundamental(q) -> sp.Matrix:
    return swap_2_tensor() * universal_R_fundamental(q)


def fibonacci_factorization_symbols():
    """Symbols for the exact Fibonacci polynomial factorizations."""
    q, a, s = sp.symbols("q a s")
    phi10 = q**4 - q**3 + q**2 - q + 1
    return q, a, s, phi10


def polynomial_identity_holds(left, right=0) -> bool:
    """Check a polynomial identity by expansion over SymPy expressions."""
    return sp.expand(left - right) == 0


def fibonacci_norm_factorization_holds() -> bool:
    """Check `(q²-q³)² + (q²-q³) - 1 = (q²-q-1) Φ₁₀(q)`."""
    q, _a, _s, phi10 = fibonacci_factorization_symbols()
    tau_q = q**2 - q**3
    return polynomial_identity_holds(tau_q**2 + tau_q - 1, (q**2 - q - 1) * phi10)


def fibonacci_artin_factorization_holds() -> bool:
    """Check the scalar Fibonacci Artin polynomial factorization.

    The diagonal phases are `r = q^4` and `t = q^7 = q^{-3}`.  After substituting
    `a = q² - q³`, the scalar constraint factors by the 10th cyclotomic
    polynomial:

    `a²(r-t)² + r t =
      q¹¹(q⁵ - q⁴ - q³ - q² + 2q + 1) Φ₁₀(q)`.
    """
    q, _a, _s, phi10 = fibonacci_factorization_symbols()
    tau_q = q**2 - q**3
    left = tau_q**2 * (q**4 - q**7) ** 2 + q**11
    right = q**11 * (q**5 - q**4 - q**3 - q**2 + 2 * q + 1) * phi10
    return polynomial_identity_holds(left, right)


def fibonacci_lean_artin_factorization_holds() -> bool:
    """Check the exact Artin factorization hardcoded in `YangBaxterProof.lean`."""
    q, _a, _s, phi10 = fibonacci_factorization_symbols()
    tau_q = q - q**4 - 1
    left = tau_q**2 * ((-q) - q**3) ** 2 + (-q) * q**3
    right = (q**10 + q**9 + 2 * q**8 + q**6 - 2 * q**5 - q**3 + q**2) * phi10
    return polynomial_identity_holds(left, right)


def fibonacci_artin_matrix_reduction_entries(a, b, r, t):
    """Generic `RBR-BRB` entry reductions in the two scalar constraints."""

    norm = a**2 + b**2 - 1
    artin = a**2 * (r - t) ** 2 + r * t
    return norm, artin, [
        (
            -t * (
                3 * a**2 * r**2
                - 3 * a**2 * r * t
                + a**2 * t**2
                + b**2 * r * t
                - r**2
                + r * t
            ),
            -(a - 1) * (a + 1) * (r - t),
        ),
        (-2 * a * b * r * t * (r - t), -a * b * (r - t)),
        (-2 * a * b * r * t * (r - t), -a * b * (r - t)),
        (
            -r * (
                a**2 * r**2
                - 3 * a**2 * r * t
                + 3 * a**2 * t**2
                + b**2 * r * t
                + r * t
                - t**2
            ),
            (a - 1) * (a + 1) * (r - t),
        ),
    ]


def fibonacci_yang_baxter_factorization_holds() -> bool:
    """Verify the finite Fibonacci Yang-Baxter reduction by polynomial expansion."""
    q, a, s, _phi10 = fibonacci_factorization_symbols()
    F = sp.Matrix([[a, s], [s, -a]])
    R = sp.diag(q**4, q**7)
    B = F * R * F
    diff = sp.Matrix(R * B * R - B * R * B)
    norm, artin, entry_coeffs = fibonacci_artin_matrix_reduction_entries(a, s, q**4, q**7)
    return all(
        sp.expand(entry - (c_norm * norm + c_artin * artin)) == 0
        for entry, (c_norm, c_artin) in zip(diff, entry_coeffs, strict=True)
    )
