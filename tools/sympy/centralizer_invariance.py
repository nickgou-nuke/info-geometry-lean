#!/usr/bin/env python3
"""Finite central-sign conjugation witness.

Checks that conjugation by `-I` is the identity on sample matrices.  Optional
`clifford` and `galgebra` are probed as navigation evidence only; Lean remains
the proof authority.
"""

from __future__ import annotations

import sympy as sp


def main() -> None:
    M = sp.Matrix([[sp.Rational(2), sp.Rational(3)], [sp.Rational(5), sp.Rational(7)]])
    I2 = sp.eye(2)
    neg = -I2
    assert neg * M * neg == M
    assert I2 * M * I2 == M
    print("SYMPY_CENTRALIZER_NEG_ONE_CONJUGATION_OK")
    print("SYMPY_CENTRALIZER_SIGN_FRAME_OK")

    try:
        import clifford  # noqa: F401
    except Exception as exc:  # pragma: no cover
        print(f"CLIFFORD_SKIPPED={type(exc).__name__}")
    else:  # pragma: no cover
        print("CLIFFORD_AVAILABLE_NAVIGATION_ONLY")

    try:
        import galgebra  # noqa: F401
    except Exception as exc:  # pragma: no cover
        print(f"GALGEBRA_SKIPPED={type(exc).__name__}")
    else:  # pragma: no cover
        print("GALGEBRA_AVAILABLE_NAVIGATION_ONLY")


if __name__ == "__main__":
    main()
