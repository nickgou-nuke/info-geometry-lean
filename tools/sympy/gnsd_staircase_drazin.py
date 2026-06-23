#!/usr/bin/env python3
"""
SymPy certificate for Guglielmi--Overton--Stewart 2015 GNSD algebra.

Checks:
* nullity increments of zero Jordan blocks recover GNSD diagonal sizes;
* the Sylvester equation decouples the `[[N,L],[0,M]]` block;
* the Appendix A Drazin formula satisfies the Drazin equations at index 2.
"""

from __future__ import annotations

import sympy as sp


def jordan_zero(k: int) -> sp.Matrix:
    return sp.Matrix(k, k, lambda i, j: sp.Integer(1) if j == i + 1 else sp.Integer(0))


def nullity(a: sp.Matrix) -> int:
    return a.cols - a.rank()


def assert_zero_matrix(m: sp.Matrix, label: str) -> None:
    if any(sp.simplify(entry) != 0 for entry in m):
        raise AssertionError(f"{label} failed:\n{m}")


def main() -> None:
    print("=== GNSD staircase / Drazin SymPy certificate ===")

    sizes = [3, 2, 1]
    jblocks = [jordan_zero(k) for k in sizes]
    a = sp.diag(*jblocks)
    nullities = [nullity(a**j) for j in range(0, 4)]
    mu = [nullities[j] - nullities[j - 1] for j in range(1, 4)]
    expected_mu = [sum(1 for k in sizes if j <= k) for j in range(1, 4)]
    exact_sizes = [mu[j - 1] - (mu[j] if j < len(mu) else 0) for j in range(1, 4)]
    assert nullities == [0, 3, 5, 6]
    assert mu == expected_mu == [3, 2, 1]
    assert exact_sizes == [1, 1, 1]
    print("PASS: Jordan nullity increments recover GNSD block-size counts")

    n = sp.Matrix([[0, 1], [0, 0]])
    m = sp.Matrix([[2, 1], [0, 3]])
    mi = m.inv()
    k = sp.Matrix([[1, 2], [-1, 1]])
    ell = k * m - n * k
    b = sp.Matrix.vstack(sp.Matrix.hstack(n, ell), sp.Matrix.hstack(sp.zeros(2), m))
    shear = sp.Matrix.vstack(
        sp.Matrix.hstack(sp.eye(2), k),
        sp.Matrix.hstack(sp.zeros(2), sp.eye(2)),
    )
    shear_inv = sp.Matrix.vstack(
        sp.Matrix.hstack(sp.eye(2), -k),
        sp.Matrix.hstack(sp.zeros(2), sp.eye(2)),
    )
    diag_nm = sp.Matrix.vstack(
        sp.Matrix.hstack(n, sp.zeros(2)),
        sp.Matrix.hstack(sp.zeros(2), m),
    )
    assert_zero_matrix(shear_inv * b * shear - diag_nm, "Sylvester decoupling")
    print("PASS: Sylvester shear decouples the GNSD coupling block")

    d = sp.Matrix.vstack(
        sp.Matrix.hstack(sp.zeros(2), k * mi),
        sp.Matrix.hstack(sp.zeros(2), mi),
    )
    assert_zero_matrix(d * b * d - d, "D B D = D")
    assert_zero_matrix(b * d - d * b, "B D = D B")
    assert_zero_matrix(b**3 * d - b**2, "B^3 D = B^2")
    print("PASS: Appendix A Drazin block formula satisfies index-2 equations")

    print("GNSD_SYMPY_CERTIFICATE_OK")


if __name__ == "__main__":
    main()
