#!/usr/bin/env python3
"""Finite 32-dimensional block-swap intertwiner laws.

This verifier checks the exact matrix identities for the UL/LR block swap:
  * W^2 = I,
  * W UL W = LR,
  * W LR W = UL,
  * W anti-commutes with the diagonal grading core.

It does not prove Tomita--Takesaki modular conjugation, CPT, anomaly shielding,
particle classification, or any Pin(5,5) representation theorem.
"""

from __future__ import annotations

import numpy as np


def assert_matrix_eq(lhs, rhs, msg: str) -> None:
    if not np.array_equal(lhs, rhs):
        raise AssertionError(f"{msg}:\n{lhs}\n!=\n{rhs}")


def main() -> None:
    i16 = np.eye(16, dtype=np.int64)
    z16 = np.zeros((16, 16), dtype=np.int64)
    i32 = np.eye(32, dtype=np.int64)

    ul = np.block([[i16, z16], [z16, z16]])
    lr = np.block([[z16, z16], [z16, i16]])
    w = np.block([[z16, i16], [i16, z16]])
    g0 = np.block([[-i16, z16], [z16, i16]])

    assert_matrix_eq(w @ w, i32, "W_involution")
    assert_matrix_eq(w @ ul @ w, lr, "W_UL_W_eq_LR")
    assert_matrix_eq(w @ lr @ w, ul, "W_LR_W_eq_UL")
    assert_matrix_eq(w @ g0, -g0 @ w, "W_g0_anticommutes")
    assert_matrix_eq(ul @ ul, ul, "UL_idempotent")
    assert_matrix_eq(lr @ lr, lr, "LR_idempotent")
    assert_matrix_eq(ul @ lr, np.zeros((32, 32), dtype=np.int64), "UL_LR_orthogonal")

    print("OK ee_intertwiner_finite_laws: W^2=I, WULW=LR, WLRW=UL, W g0 = -g0 W")
    print("scope: finite 32D block-swap laws only; no Tomita--Takesaki, CPT, anomaly, or particle theorem claimed")


if __name__ == "__main__":
    main()
