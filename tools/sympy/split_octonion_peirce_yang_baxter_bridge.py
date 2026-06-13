#!/usr/bin/env python3
"""Finite Peirce-payload/Yang-Baxter bridge witness.

Lean twin:
    InfoGeometry.OperatorAlgebra.SplitOctonionPeirceYangBaxterBridge

Scope boundary:
    This script checks only finite Peirce projection-compression payload
    accounting and a finite permutation-level Yang-Baxter/Artin rewrite.
    It does not construct an R-matrix from split octonions, a full braid group
    representation, Yang-Baxter for split-octonion multiplication, wallpaper
    forcing, Clifford-volume invariance, or arbitrary q-Casimir preservation.
"""

from __future__ import annotations

import sympy as sp


Matrix = sp.MutableDenseMatrix
Permutation = tuple[int, int, int]


def compose(left: Permutation, right: Permutation) -> Permutation:
    """Return left after right on the finite set {0,1,2}."""
    return tuple(left[right[i]] for i in range(3))


def eval_braid_word(word: list[int]) -> Permutation:
    """Evaluate the two-generator S3 braid shadow."""
    swaps: dict[int, Permutation] = {
        0: (1, 0, 2),
        1: (0, 2, 1),
    }
    perm: Permutation = (0, 1, 2)
    for letter in reversed(word):
        perm = compose(swaps[letter], perm)
    return perm


def peirce_transition(payload: Matrix) -> Matrix:
    e_plus = sp.Matrix([[1, 0], [0, 0]])
    e_minus = sp.Matrix([[0, 0], [0, 1]])
    return e_plus * payload * e_plus + e_minus * payload * e_minus


def matrix_key(payload: Matrix) -> tuple[tuple[sp.Expr, ...], ...]:
    return tuple(tuple(sp.simplify(payload[row, col]) for col in range(payload.cols))
                 for row in range(payload.rows))


def peirce_braid_readout(word: list[int], payload: Matrix) -> tuple[Permutation, tuple[tuple[sp.Expr, ...], ...]]:
    return eval_braid_word(word), matrix_key(peirce_transition(payload))


def verify_peirce_payloads() -> None:
    one = sp.eye(2)
    e_plus = sp.Matrix([[1, 0], [0, 0]])
    e_minus = sp.Matrix([[0, 0], [0, 1]])
    h = e_plus - e_minus
    up = sp.Matrix([[0, 1], [0, 0]])
    down = sp.Matrix([[0, 0], [1, 0]])
    zero = sp.zeros(2)

    assert peirce_transition(one) == one
    assert peirce_transition(e_plus) == e_plus
    assert peirce_transition(e_minus) == e_minus
    assert peirce_transition(h) == h
    assert peirce_transition(up) == zero
    assert peirce_transition(down) == zero


def verify_yang_baxter_payload_readout() -> None:
    left_word = [0, 1, 0]
    right_word = [1, 0, 1]
    assert eval_braid_word(left_word) == eval_braid_word(right_word)

    payloads = [
        sp.eye(2),
        sp.Matrix([[1, 0], [0, 0]]),
        sp.Matrix([[0, 0], [0, 1]]),
        sp.Matrix([[1, 0], [0, -1]]),
        sp.Matrix([[0, 1], [0, 0]]),
        sp.Matrix([[0, 0], [1, 0]]),
    ]
    for payload in payloads:
        assert peirce_braid_readout(left_word, payload) == peirce_braid_readout(right_word, payload)


def main() -> None:
    verify_peirce_payloads()
    verify_yang_baxter_payload_readout()
    print("SPLIT_OCTONION_PEIRCE_YANG_BAXTER_BRIDGE_OK")
    print("scope=finite Peirce payload compression plus finite permutation Yang-Baxter rewrite only")


if __name__ == "__main__":
    main()
