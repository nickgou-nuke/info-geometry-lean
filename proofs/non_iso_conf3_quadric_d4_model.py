#!/usr/bin/env python3
"""Candidate finite cdga model for the D=4 non-isotropic 3-point problem.

For one nondegenerate quadric complement C^4 \\ {q=0}, the map
q : C^4 \\ {q=0} -> C* suggests two finite classes:

  alpha = dlog(q), degree 1
  beta  = affine-quadric fiber class, degree 3

For three pairs we use generators:

  a12,a23,a13 in degree 1
  b12,b23,b13 in degree 3

All six generators are odd, so this starts as an exterior algebra.  We then
impose the Arnold-Orlik-Solomon alpha relation

  a12*a23 - a12*a13 + a23*a13 = 0.

This is not the final D=4 theorem: beta-interaction/Gysin relations are left
as the next geometric layer.  The script computes the Hilbert ranks of this
first corrected candidate quotient.
"""

from __future__ import annotations

from collections import defaultdict
from fractions import Fraction
from itertools import combinations

import sympy as sp


GENERATORS = ["a12", "a23", "a13", "b12", "b23", "b13"]
DEGREES = [1, 1, 1, 3, 3, 3]
N = len(GENERATORS)


def degree(mask: int) -> int:
    return sum(DEGREES[i] for i in range(N) if mask & (1 << i))


def exterior_mul(left: int, right: int) -> tuple[int, int] | None:
    """Return (sign, mask) for exterior monomial product, or None if square."""
    if left & right:
        return None
    inversions = 0
    for i in range(N):
        if left & (1 << i):
            for j in range(i):
                if right & (1 << j):
                    inversions += 1
    sign = -1 if inversions % 2 else 1
    return sign, left | right


def multiply_vector(vec: dict[int, Fraction], monomial: int) -> dict[int, Fraction]:
    out: dict[int, Fraction] = defaultdict(Fraction)
    for mask, coeff in vec.items():
        product = exterior_mul(mask, monomial)
        if product is None:
            continue
        sign, new_mask = product
        out[new_mask] += coeff * sign
    return {mask: coeff for mask, coeff in out.items() if coeff}


def vector_to_row(vec: dict[int, Fraction], basis: list[int]) -> list[sp.Rational]:
    return [sp.Rational(vec.get(mask, 0).numerator, vec.get(mask, 0).denominator) for mask in basis]


def monomial_name(mask: int) -> str:
    names = [GENERATORS[i] for i in range(N) if mask & (1 << i)]
    return "1" if not names else "*".join(names)


def main() -> None:
    a12 = 1 << 0
    a23 = 1 << 1
    a13 = 1 << 2

    relation: dict[int, Fraction] = {}
    for coeff, left, right in [
        (Fraction(1), a12, a23),
        (Fraction(-1), a12, a13),
        (Fraction(1), a23, a13),
    ]:
        product = exterior_mul(left, right)
        assert product is not None
        sign, mask = product
        relation[mask] = relation.get(mask, Fraction(0)) + coeff * sign

    all_masks = list(range(1 << N))
    max_degree = sum(DEGREES)
    quotient_ranks: dict[int, int] = {}
    ideal_ranks: dict[int, int] = {}

    for deg in range(max_degree + 1):
        basis = [mask for mask in all_masks if degree(mask) == deg]
        ideal_vectors = []
        for multiplier in all_masks:
            if degree(multiplier) + 2 != deg:
                continue
            product = multiply_vector(relation, multiplier)
            if product:
                ideal_vectors.append(vector_to_row(product, basis))

        if ideal_vectors:
            matrix = sp.Matrix(ideal_vectors)
            ideal_rank = matrix.rank()
        else:
            ideal_rank = 0
        ideal_ranks[deg] = ideal_rank
        quotient_ranks[deg] = len(basis) - ideal_rank

    assert quotient_ranks[0] == 1
    assert quotient_ranks[1] == 3
    assert quotient_ranks[2] == 2

    print("non_iso_conf3_quadric_d4_model.py: corrected D=4 candidate quotient")
    print("generators:", ", ".join(f"{g}:{d}" for g, d in zip(GENERATORS, DEGREES)))
    print("relation: a12*a23 - a12*a13 + a23*a13 = 0")
    print("degree : exterior_dim -> ideal_rank -> quotient_rank")
    for deg in range(max_degree + 1):
        basis_dim = sum(1 for mask in all_masks if degree(mask) == deg)
        if basis_dim or quotient_ranks[deg]:
            print(f"{deg:2d}: {basis_dim:2d} -> {ideal_ranks[deg]:2d} -> {quotient_ranks[deg]:2d}")

    print("basis in degree 2 after quotient can be represented by:")
    print("  a12*a23, a12*a13")
    print("beta/Gysin interaction relations are not imposed in this first candidate.")


if __name__ == "__main__":
    main()
