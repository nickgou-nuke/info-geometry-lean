#!/usr/bin/env python3
"""Finite witness for the five-graded Möbius/Witten globality packet.

Navigation-only witness: Lean theorems remain authoritative.
"""

import sympy as sp


def main() -> None:
    e_plus = sp.Matrix([[0, 1], [0, 0]])
    e_minus = sp.Matrix([[0, 0], [1, 0]])
    I2 = sp.eye(2)

    assert e_plus**2 == sp.zeros(2)
    assert e_minus**2 == sp.zeros(2)
    assert e_plus * e_minus + e_minus * e_plus == I2

    p_plus = e_plus * e_minus
    p_minus = e_minus * e_plus
    assert p_plus**2 == p_plus
    assert p_minus**2 == p_minus
    assert p_plus * p_minus == sp.zeros(2)
    assert p_minus * p_plus == sp.zeros(2)
    assert p_plus + p_minus == I2

    chi_global_4 = sp.diag(1, -1, -1, 1)
    moebius_strip_4 = sp.diag(1, -1, 1, -1)
    assert sp.trace(chi_global_4) == 0
    assert sp.trace(moebius_strip_4 * chi_global_4) == 0

    witten = [1, -1, 1, -1]
    assert sum(witten) == 0

    # Toy finite compensation ledger: total = visible + reservoir is constant.
    visible = [7, 5, 2]
    grade_two = [3, 5, 8]
    assert [v + g for v, g in zip(visible, grade_two)] == [10, 10, 10]
    assert visible[0] - visible[-1] == grade_two[-1] - grade_two[0]

    print("SYMPY_LIGHTCONE_COMPENSATION_PROJECTORS_OK")
    print("SYMPY_MOBIUS_CHIRAL_TRACE_ZERO_OK")
    print("SYMPY_WITTEN_FOUR_LAYER_SUM_ZERO_OK")
    print("SYMPY_RECURSIVE_COMPENSATION_TOY_LEDGER_OK")


if __name__ == "__main__":
    main()
