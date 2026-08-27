"""Discover the four residual-pivot cases for the native flag closure.

This script is evidence only.  It does not prove a Lean theorem.  The matrix
convention and peel order are inherited from ``verify_full_peel_residual_cas``.
Its output is used to choose the finite, explicit readback obligations that
Lean must verify independently.
"""

from collections import Counter

from verify_flag_stabilizer_full_peel_cas import subgroup
from verify_full_peel_residual_cas import mm, s_gens


def residual_case(element):
    pc0, _, _, _, pc5, pc6 = s_gens
    q1 = mm(pc6, s_gens[1])
    q2 = mm(pc6, s_gens[2])

    after_zero = mm(element, pc0) if int(element[2, 7]) else element
    pivot_one = int(after_zero[3, 2])
    after_one = mm(after_zero, q1) if pivot_one else after_zero
    pivot_two = int(after_one[3, 7])
    after_two = mm(after_one, q2) if pivot_two else after_one
    pivot_five = int(after_two[4, 2])
    return pivot_two, pivot_five


def main():
    elements = subgroup([s_gens[0], s_gens[1], s_gens[2], s_gens[4]])
    counts = Counter(residual_case(element) for element in elements)
    expected = {(a, b): 16 for a in (0, 1) for b in (0, 1)}
    print("FLAG_CLOSURE_CARD=", len(elements))
    print("RESIDUAL_CASE_COUNTS=", dict(sorted(counts.items())))
    assert len(elements) == 64
    assert counts == expected
    print("RESIDUAL_CASE_CERTIFICATE=PASS")


if __name__ == "__main__":
    main()
