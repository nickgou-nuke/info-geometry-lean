#!/usr/bin/env python3
"""
Ross Street, "Braids among the groups" -- exact computational witnesses.

This script checks two theorem-safe finite shadows:

1. Artin's braid-group action on the free group F_3:
      beta_i(x_i)     = x_{i+1}
      beta_i(x_{i+1}) = x_{i+1} x_i x_{i+1}^{-1}
      beta_i(x_j)     = x_j otherwise
   and verifies beta_1 beta_2 beta_1 = beta_2 beta_1 beta_2 on generators.

2. The permutation/Coxeter shadow obtained by imposing sigma_i^2 = 1, realised
   as exact Euclidean reflection matrices swapping adjacent basis vectors.

The optional Galgebra package is probed, but not required for the certified
checks because it is not installed in the default repo environment.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Dict, Iterable, Tuple

import sympy as sp

Generator = int
Word = Tuple[Generator, ...]


def reduce_word(word: Iterable[Generator]) -> Word:
    """Freely reduce a word encoded by signed generator indices."""
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
        pieces: list[Word] = []
        for g in word:
            img = self.images[abs(g)]
            pieces.append(img if g > 0 else inv_word(img))
        return mul_word(*pieces)

    def then(self, other: "FreeAutomorphism") -> "FreeAutomorphism":
        """Composition: self after other."""
        return FreeAutomorphism({i: self.apply_word(other.images[i]) for i in self.images})


def beta(i: int, n: int) -> FreeAutomorphism:
    images = {j: (j,) for j in range(1, n + 1)}
    images[i] = (i + 1,)
    images[i + 1] = (i + 1, i, -(i + 1))
    return FreeAutomorphism(images)


def word_str(word: Word) -> str:
    if not word:
        return "1"
    return " ".join(f"x{g}" if g > 0 else f"x{-g}^-1" for g in word)


def verify_artin_free_group_action() -> None:
    print("--- Exact free-group Artin action on F3 ---")
    b1 = beta(1, 3)
    b2 = beta(2, 3)
    lhs = b1.then(b2).then(b1)
    rhs = b2.then(b1).then(b2)
    for i in range(1, 4):
        if lhs.images[i] != rhs.images[i]:
            raise AssertionError(
                f"Artin relation failed on x{i}: {word_str(lhs.images[i])} != {word_str(rhs.images[i])}"
            )
        print(f"  x{i} -> {word_str(lhs.images[i])}")
    print("PASS: beta1 beta2 beta1 = beta2 beta1 beta2 on F3 generators.")


def reflection_swap_matrix(i: int, j: int, n: int) -> sp.Matrix:
    """Exact reflection in the hyperplane x_i=x_j; this swaps e_i and e_j."""
    normal = sp.zeros(n, 1)
    normal[i, 0] = 1
    normal[j, 0] = -1
    return sp.eye(n) - sp.Rational(2, 1) * (normal * normal.T) / (normal.T * normal)[0, 0]


def verify_exact_reflection_shadow() -> None:
    print("\n--- Exact reflection/Coxeter S3 shadow ---")
    s1 = reflection_swap_matrix(0, 1, 3)
    s2 = reflection_swap_matrix(1, 2, 3)
    I3 = sp.eye(3)
    if s1 * s1 != I3 or s2 * s2 != I3:
        raise AssertionError("reflection generators are not involutions")
    if s1 * s2 * s1 != s2 * s1 * s2:
        raise AssertionError("Coxeter braid relation failed")
    print("PASS: sigma_i^2 = I for exact reflection matrices.")
    print("PASS: sigma1 sigma2 sigma1 = sigma2 sigma1 sigma2 in the S3 shadow.")
    print("sigma1=")
    print(s1)
    print("sigma2=")
    print(s2)


def report_optional_galgebra() -> None:
    try:
        import galgebra  # noqa: F401
    except Exception as exc:  # pragma: no cover - environment report only
        print(f"\nINFO: optional Galgebra rotor lane unavailable: {exc.__class__.__name__}: {exc}")
        print("INFO: exact reflection matrices above are the certified fallback witness.")
    else:  # pragma: no cover - depends on optional package
        print("\nINFO: optional Galgebra package is available; matrix witness remains authoritative here.")


if __name__ == "__main__":
    verify_artin_free_group_action()
    verify_exact_reflection_shadow()
    report_optional_galgebra()
    print("\nAll exact pointed-group braid witnesses passed.")
