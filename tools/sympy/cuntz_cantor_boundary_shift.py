"""Finite checks for binary Cuntz-style shifts on Cantor cylinders.

This mirrors InfoGeometry.Canonical.CuntzCantorBoundaryShift:

* prepend a branch bit to a finite boundary word;
* drop the head bit;
* verify branch disjointness and cover on a finite window;
* verify that pulling back a stage n+1 cylinder along a branch yields a
  stage n cylinder.

No C*-completion, Hilbert-space partial isometry, KMS dynamics, or zeta theorem
is claimed here.
"""

from __future__ import annotations

import itertools
import sympy as sp


BitWord = tuple[int, ...]


def prepend_bit(bit: int, word: BitWord) -> BitWord:
    return (bit,) + word


def tail(word: BitWord) -> BitWord:
    return word[1:]


def all_words(length: int) -> list[BitWord]:
    return list(itertools.product([0, 1], repeat=length))


def branch_prefix(bit: int, word: BitWord) -> BitWord:
    return prepend_bit(bit, word)


def cylinder(values: dict[BitWord, sp.Expr], word: BitWord) -> sp.Expr:
    return values[word]


def verify_tail_prepend() -> None:
    for n in range(5):
        for word in all_words(n):
            for bit in [0, 1]:
                assert tail(prepend_bit(bit, word)) == word
                assert prepend_bit(bit, word)[0] == bit


def verify_disjoint_cover() -> None:
    for n in range(1, 6):
        words = set(all_words(n))
        left = {prepend_bit(0, word) for word in all_words(n - 1)}
        right = {prepend_bit(1, word) for word in all_words(n - 1)}
        assert left | right == words
        assert left & right == set()


def verify_cylinder_branch_pullback() -> None:
    for n in range(5):
        symbols = sp.symbols(f"a0:{2 ** (n + 1)}")
        stage_np1_words = all_words(n + 1)
        values = dict(zip(stage_np1_words, symbols))

        for bit in [0, 1]:
            pulled_values = {
                word: values[branch_prefix(bit, word)]
                for word in all_words(n)
            }
            for word in all_words(n):
                assert cylinder(values, prepend_bit(bit, word)) == cylinder(pulled_values, word)


def main() -> None:
    verify_tail_prepend()
    verify_disjoint_cover()
    verify_cylinder_branch_pullback()
    print("Cuntz-Cantor finite boundary shifts verified")


if __name__ == "__main__":
    main()

