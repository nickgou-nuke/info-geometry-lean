#!/usr/bin/env python3
"""Finite-dimensional Cuntz-induction bridge for the split-octonion Peirce pair.

This witness connects the committed split-octonion Peirce/Witt identities to the
repo's finite Cuntz/UHF induction formulas only at the projection-accounting
level.

It verifies the exact 2x2 partial-isometry model:
  S_L = |0><0|, S_R = |1><1|,
  P_L = S_L S_L^* = ePlus, P_R = S_R S_R^* = eMinus,
  P_L + P_R = I,
  T(X) = P_L X P_L + P_R X P_R,
  T(I)=I, T(P_L)=P_L, T(P_R)=P_R,
  T(H)=H, and the off-diagonal Witt slots are killed by T.

Boundary: this is a finite-dimensional projection/compression formula.  It does
not assert that the split-octonion algebra carries Cuntz O_2 isometries, a C*-
completion, a braid representation, or a wallpaper forcing theorem.
"""

from __future__ import annotations

import sympy as sp


def main() -> None:
    I = sp.eye(2)
    e_plus = sp.Matrix([[1, 0], [0, 0]])
    e_minus = sp.Matrix([[0, 0], [0, 1]])
    H = e_plus - e_minus
    up = sp.Matrix([[0, 1], [0, 0]])
    down = sp.Matrix([[0, 0], [1, 0]])

    S_L = e_plus
    S_R = e_minus
    P_L = S_L * S_L.T
    P_R = S_R * S_R.T

    def transition(X: sp.Matrix) -> sp.Matrix:
        return sp.simplify(P_L * X * P_L + P_R * X * P_R)

    assert P_L == e_plus
    assert P_R == e_minus
    assert P_L + P_R == I
    assert P_L * P_L == P_L
    assert P_R * P_R == P_R
    assert P_L * P_R == sp.zeros(2)
    assert P_R * P_L == sp.zeros(2)

    assert transition(I) == I
    assert transition(e_plus) == e_plus
    assert transition(e_minus) == e_minus
    assert transition(H) == H
    assert transition(up) == sp.zeros(2)
    assert transition(down) == sp.zeros(2)

    # Compatibility with the Peirce-Witt packet.
    assert up * down == e_plus
    assert down * up == e_minus
    assert up * down - down * up == H
    assert up * down + down * up == I

    print("SPLIT_OCTONION_CUNTZ_INDUCTION_BRIDGE_OK")
    print("scope: finite-dimensional Peirce projection/UHF-transition formulas only")


if __name__ == "__main__":
    main()
