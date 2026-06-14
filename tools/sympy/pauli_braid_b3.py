#!/usr/bin/env python3
"""Finite Pauli B3 braid witness.

Exact SymPy matrix check for A=I+iσ1, B=I+iσ2:
    A B A = B A B = 2 i (σ1 + σ2).

Optional `clifford` and `galgebra` imports are probed as navigation evidence
only; Lean is the proof authority.
"""

from __future__ import annotations

import sympy as sp


def main() -> None:
    I = sp.I
    one = sp.eye(2)
    s1 = sp.Matrix([[0, 1], [1, 0]])
    s2 = sp.Matrix([[0, -I], [I, 0]])
    s3 = sp.Matrix([[1, 0], [0, -1]])
    A = one + I * s1
    B = one + I * s2

    assert s1 * s1 == one
    assert s2 * s2 == one
    assert s3 * s3 == one
    assert s1 * s2 == -s2 * s1
    assert s1 * s2 == I * s3
    assert sp.simplify(A * B * A - B * A * B) == sp.zeros(2)
    assert sp.simplify(A * B * A - 2 * I * (s1 + s2)) == sp.zeros(2)

    print("SYMPY_PAULI_B3_SQUARES_OK")
    print("SYMPY_PAULI_B3_ANTICOMM_OK")
    print("SYMPY_PAULI_B3_BRAID_OK")
    print("SYMPY_PAULI_B3_TRIPLE_PRODUCT_OK")

    try:
        import clifford  # noqa: F401
    except Exception as exc:  # pragma: no cover - optional dependency
        print(f"CLIFFORD_SKIPPED={type(exc).__name__}")
    else:  # pragma: no cover - optional dependency
        print("CLIFFORD_AVAILABLE_NAVIGATION_ONLY")

    try:
        import galgebra  # noqa: F401
    except Exception as exc:  # pragma: no cover - optional dependency
        print(f"GALGEBRA_SKIPPED={type(exc).__name__}")
    else:  # pragma: no cover - optional dependency
        print("GALGEBRA_AVAILABLE_NAVIGATION_ONLY")


if __name__ == "__main__":
    main()
