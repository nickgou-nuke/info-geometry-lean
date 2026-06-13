#!/usr/bin/env sage -python
"""
Sage exact witness for Ross Street's pointed-group braid action.

Checks the Artin braid relation on a free-word model for F3 and the S3
Coxeter/reflection quotient with exact integer matrices.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Dict, Iterable, Tuple

from sage.all import Matrix, QQ, identity_matrix

Generator = int
Word = Tuple[Generator, ...]


def reduce_word(word: Iterable[Generator]) -> Word:
    stack: list[Generator] = []
    for g in word:
        if stack and stack[-1] == -g:
            stack.pop()
        else:
            stack.append(g)
    return tuple(stack)


def inv_word(word: Word) -> Word:
    return tuple(-g for g in reversed(word))


def mul_word(*words: Word) -> Word:
    out: Word = ()
    for w in words:
        out = reduce_word(out + w)
    return out


@dataclass(frozen=True)
class FreeAutomorphism:
    images: Dict[int, Word]

    def apply_word(self, word: Word) -> Word:
        return mul_word(*(self.images[abs(g)] if g > 0 else inv_word(self.images[abs(g)]) for g in word))

    def then(self, other: "FreeAutomorphism") -> "FreeAutomorphism":
        return FreeAutomorphism({i: self.apply_word(other.images[i]) for i in self.images})


def beta(i: int, n: int) -> FreeAutomorphism:
    images = {j: (j,) for j in range(1, n + 1)}
    images[i] = (i + 1,)
    images[i + 1] = (i + 1, i, -(i + 1))
    return FreeAutomorphism(images)


def verify_artin_action() -> None:
    b1 = beta(1, 3)
    b2 = beta(2, 3)
    lhs = b1.then(b2).then(b1)
    rhs = b2.then(b1).then(b2)
    for i in range(1, 4):
        if lhs.images[i] != rhs.images[i]:
            raise AssertionError(f"Artin relation failed on x{i}")
    print("PASS: Sage free-word Artin action on F3")


def reflection_swap(i: int, j: int, n: int):
    normal = Matrix(QQ, n, 1, [1 if k == i else (-1 if k == j else 0) for k in range(n)])
    return identity_matrix(QQ, n) - 2 * (normal * normal.transpose()) / (normal.transpose() * normal)[0, 0]


def verify_reflection_shadow() -> None:
    s1 = reflection_swap(0, 1, 3)
    s2 = reflection_swap(1, 2, 3)
    I3 = identity_matrix(QQ, 3)
    assert s1 * s1 == I3
    assert s2 * s2 == I3
    assert s1 * s2 * s1 == s2 * s1 * s2
    print("PASS: Sage exact S3 reflection quotient shadow")


if __name__ == "__main__":
    verify_artin_action()
    verify_reflection_shadow()
    print("POINTED_GROUPS_BRAID_SAGE_OK")
