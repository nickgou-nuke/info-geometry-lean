#!/usr/bin/env python3
"""Finite witness for Kashiwara-Cuntz symbolic cohomology.

This mirrors `InfoGeometry.Canonical.KashiwaraCuntzCohomology`:

* lowering is binary prefixing;
* raising is partial deletion of a matching head bit;
* the empty word is annihilated by both raising maps;
* the mirror involution swaps left and right branches.

The matrix check is deliberately finite and truncated.  It verifies the
section identity R_b L_b = I on the source block of words whose lowered image
still lies inside the depth cutoff.
"""

from __future__ import annotations

from itertools import product

import sympy as sp


Word = tuple[int, ...]


def words_upto(depth: int) -> list[Word]:
    words: list[Word] = [()]
    for length in range(1, depth + 1):
        words.extend(tuple(bits) for bits in product((0, 1), repeat=length))
    return words


def lower(bit: int, word: Word) -> Word:
    return (bit,) + word


def raise_branch(bit: int, word: Word) -> Word | None:
    if not word:
        return None
    if word[0] == bit:
        return word[1:]
    return None


def mirror(word: Word) -> Word:
    return tuple(1 - bit for bit in word)


def lowering_matrix(bit: int, basis: list[Word], index: dict[Word, int], depth: int) -> sp.Matrix:
    mat = sp.zeros(len(basis), len(basis))
    for word in basis:
        image = lower(bit, word)
        if len(image) <= depth:
            mat[index[image], index[word]] = 1
    return mat


def raising_matrix(bit: int, basis: list[Word], index: dict[Word, int]) -> sp.Matrix:
    mat = sp.zeros(len(basis), len(basis))
    for word in basis:
        image = raise_branch(bit, word)
        if image is not None:
            mat[index[image], index[word]] = 1
    return mat


def projector_source(basis: list[Word], depth: int) -> sp.Matrix:
    mat = sp.zeros(len(basis), len(basis))
    for i, word in enumerate(basis):
        if len(word) < depth:
            mat[i, i] = 1
    return mat


def main() -> None:
    depth = 4
    basis = words_upto(depth)
    index = {word: i for i, word in enumerate(basis)}

    symbolic_checks = []
    for word in basis:
        symbolic_checks.append(raise_branch(0, lower(0, word)) == word)
        symbolic_checks.append(raise_branch(1, lower(1, word)) == word)
        symbolic_checks.append(mirror(mirror(word)) == word)
        symbolic_checks.append(mirror(lower(0, word)) == lower(1, mirror(word)))
        symbolic_checks.append(mirror(lower(1, word)) == lower(0, mirror(word)))

    root_annihilation = raise_branch(0, ()) is None and raise_branch(1, ()) is None

    L0 = lowering_matrix(0, basis, index, depth)
    L1 = lowering_matrix(1, basis, index, depth)
    R0 = raising_matrix(0, basis, index)
    R1 = raising_matrix(1, basis, index)
    P_source = projector_source(basis, depth)

    left_section = R0 * L0 * P_source == P_source
    right_section = R1 * L1 * P_source == P_source

    print("Kashiwara-Cuntz finite symbolic witness")
    print(f"1. Checked words up to depth {depth}: {len(basis)}")
    print(f"2. Lowering/raising/mirror symbolic identities: {all(symbolic_checks)}")
    print(f"3. Root word raising-annihilation: {root_annihilation}")
    print(f"4. Matrix section R_left * L_left = I on source block: {left_section}")
    print(f"5. Matrix section R_right * L_right = I on source block: {right_section}")


if __name__ == "__main__":
    main()
