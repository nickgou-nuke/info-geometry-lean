#!/usr/bin/env python3
"""Finite witness for the split-idempotent 5-weight socket.

Uses the algebra K×K with E=(2,0), Ebar=(0,2), so E²=2E, Ebar²=2Ebar,
and E*Ebar=0. This mirrors the Lean normalization; it is witness evidence only.
"""

from __future__ import annotations


def add(x, y):
    return (x[0] + y[0], x[1] + y[1])


def mul(x, y):
    return (x[0] * y[0], x[1] * y[1])


def smul(c, x):
    return (c * x[0], c * x[1])


def main() -> None:
    E = (2, 0)
    Eb = (0, 2)
    assert mul(E, Eb) == (0, 0)
    assert mul(Eb, E) == (0, 0)
    assert mul(E, E) == smul(2, E)
    assert mul(Eb, Eb) == smul(2, Eb)

    a_plus = 3
    a_minus = 5
    a = add(smul(a_plus, E), smul(a_minus, Eb))
    assert mul(a, E) == smul(2 * a_plus, E)
    assert mul(a, Eb) == smul(2 * a_minus, Eb)

    print("SYMPY_FIVE_GRADED_TKK_IDEMPOTENTS_OK")
    print("SYMPY_FIVE_GRADED_TKK_PROJECTION_E_OK")
    print("SYMPY_FIVE_GRADED_TKK_PROJECTION_EBAR_OK")


if __name__ == "__main__":
    main()
