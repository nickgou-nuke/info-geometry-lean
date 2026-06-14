#!/usr/bin/env python3
"""SymPy witness for q55 zero/null/generic strata.

Finite exact checks only; not a group orbit classification.
"""

from __future__ import annotations

import sympy as sp


def q55(v: sp.Matrix) -> sp.Expr:
    return sum(v[i] ** 2 for i in range(5)) - sum(v[i] ** 2 for i in range(5, 10))


def main() -> None:
    zero = sp.zeros(10, 1)
    e0 = sp.eye(10).col(0)
    e5 = sp.eye(10).col(5)
    null = e0 + e5

    assert q55(zero) == 0
    assert q55(null) == 0 and null != zero
    assert q55(e0) == 1
    assert q55(e5) == -1
    for v in (zero, null, e0, e5):
        assert q55(-v) == q55(v)

    print("SPINOR_ORBIT_Q55_ZERO_OK")
    print("SPINOR_ORBIT_Q55_NULL_OK")
    print("SPINOR_ORBIT_Q55_GENERIC_POS_OK")
    print("SPINOR_ORBIT_Q55_GENERIC_NEG_OK")
    print("SPINOR_ORBIT_Q55_NEGALL_PRESERVES_OK")


if __name__ == "__main__":
    main()
