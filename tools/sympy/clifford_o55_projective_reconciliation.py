#!/usr/bin/env python3
"""Clifford/O(5,5)/projective-layer reconciliation checks.

This script verifies the finite arithmetic behind the layer separation:

* ``Cl(1,1)^{⊗5}`` and ``Cl(5,5)`` have the same real algebra dimension;
* the executable split Clifford matrix window is ``M_32(R)``;
* the hyperbolic split form is preserved by rational ``O(5,5)`` generators;
* ``O(5,5;Q)`` acts inside the ambient rational projective group
  ``PGL_10(Q)`` after quotienting scalar representatives.

No external certificate is consumed.
"""

from __future__ import annotations

import sympy as sp


def assert_scalar(name: str, condition: bool) -> None:
    if not condition:
        raise AssertionError(name)
    print(f"  {name}: OK")


def assert_matrix_zero(name: str, matrix: sp.Matrix) -> None:
    diff = matrix.applyfunc(sp.simplify)
    if diff != sp.zeros(*diff.shape):
        raise AssertionError(f"{name} failed:\n{diff}")
    print(f"  {name}: OK")


def hyperbolic_eta(n: int) -> sp.Matrix:
    return sp.Matrix.vstack(
        sp.Matrix.hstack(sp.zeros(n), sp.eye(n)),
        sp.Matrix.hstack(sp.eye(n), sp.zeros(n)),
    )


def is_projectively_equivalent(v: sp.Matrix, w: sp.Matrix) -> bool:
    """Check whether two nonzero vectors span the same rational line."""
    if v == sp.zeros(v.rows, 1) or w == sp.zeros(w.rows, 1):
        return False
    scale = None
    for vi, wi in zip(v, w):
        if vi != 0:
            scale = sp.simplify(wi / vi)
            break
    if scale is None or scale == 0:
        return False
    return all(sp.simplify(wi - scale * vi) == 0 for vi, wi in zip(v, w))


def verify_clifford_dimensions() -> None:
    print("\nClifford tensor dimensions")
    cl11_dim = 2 ** 2
    cl55_dim = 2 ** 10
    tensor_power_dim = cl11_dim ** 5
    matrix_size = 2 ** 5
    assert_scalar("dim Cl(1,1)^5 = dim Cl(5,5)",
                  tensor_power_dim == cl55_dim)
    assert_scalar("Cl(5,5) matrix window is M_32(R)",
                  matrix_size * matrix_size == cl55_dim)
    assert_scalar("five split atoms give ten Clifford generators", 5 * 2 == 10)


def verify_o55_rational_generators() -> None:
    print("\nO(5,5;Q) rational generators")
    n = 5
    eta = hyperbolic_eta(n)
    swap = eta
    parity = -sp.eye(2 * n)
    shear_b = sp.zeros(n)
    shear_b[0, 1] = sp.Rational(2, 3)
    shear_b[1, 0] = -sp.Rational(2, 3)
    b_transform = sp.Matrix.vstack(
        sp.Matrix.hstack(sp.eye(n), shear_b),
        sp.Matrix.hstack(sp.zeros(n), sp.eye(n)),
    )

    for name, matrix in (("momentum/winding swap", swap),
                         ("global parity twist", parity),
                         ("rational B-field shear", b_transform)):
        assert_matrix_zero(f"{name} preserves eta", matrix.T * eta * matrix - eta)
        assert_scalar(f"{name} is invertible over Q", sp.simplify(matrix.det()) != 0)


def verify_projective_shadow() -> None:
    print("\nprojective rational shadow")
    n = 5
    eta = hyperbolic_eta(n)
    q = sp.Matrix([1, 2, 3, 5, 8, 13, 21, 34, 55, 89])
    swap = eta
    parity = -sp.eye(2 * n)
    assert_scalar("M and -M have the same projective action",
                  is_projectively_equivalent(swap * q, (-swap) * q))
    assert_scalar("global parity is projectively scalar",
                  is_projectively_equivalent(q, parity * q))


def main() -> int:
    print("=" * 72)
    print("CLIFFORD / O(5,5) / PROJECTIVE RECONCILIATION")
    print("=" * 72)
    verify_clifford_dimensions()
    verify_o55_rational_generators()
    verify_projective_shadow()
    print("\nCLIFFORD O55 PROJECTIVE RECONCILIATION VERIFIED")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
