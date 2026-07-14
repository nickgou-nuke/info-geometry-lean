#!/usr/bin/env python3
"""Exact Sage audit for Kingdon/Zorn cyclic trivector and Peirce signs.

This is external evidence only. Lean owner theorems remain authoritative.
Run with the repository Sage environment, for example:
  /home/goutev/miniforge3/envs/sage/bin/python tools/sage/kingdon_trivector_sign_audit.py
"""

from itertools import permutations

from sage.algebras.octonion_algebra import OctonionAlgebra
from sage.all import QQ


def main() -> None:
    algebra = OctonionAlgebra(QQ, -1, -1, 1)
    basis = list(algebra.basis())
    one = algebra.one()

    triples = []
    for i, j, k in permutations(range(1, 8), 3):
        e0, e1, e2 = basis[i], basis[j], basis[k]
        if not all(e * e == one for e in (e0, e1, e2)):
            continue
        if not (e0 * e1 == -(e1 * e0) and e1 * e2 == -(e2 * e1)
                and e0 * e2 == -(e2 * e0)):
            continue
        if (e0 * e1) * e2 != e2 * (e1 * e0):
            continue
        triples.append((i, j, k))

    assert len(triples) == 24

    for i, j, k in triples:
        generators = [basis[i], basis[j], basis[k]]
        e0, e1, e2 = generators
        q0 = e1 * e2
        upper0 = (e0 - q0) / 2
        lower0 = (e0 + q0) / 2
        diagonal_upper = upper0 * lower0
        diagonal_lower = lower0 * upper0

        for axis in (1, 2):
            ea = generators[axis]
            eb = generators[2 if axis == 1 else 0]
            ec = generators[0 if axis == 1 else 1]
            qa = eb * ec
            upper = (ea - qa) / 2
            lower = (ea + qa) / 2

            assert diagonal_lower * upper == 0
            assert upper * diagonal_upper == 0
            assert diagonal_upper * lower == 0
            assert lower * diagonal_lower == 0

        trivector = e0 * (e1 * e2)
        assert trivector * e1 == -(e2 * e0)
        assert trivector * e2 == e1 * e0

    sample = triples[0]
    print(f"verified_admissible_triples={len(triples)}")
    print(f"sample_basis_indices={sample}")
    print("trivector_signs=verified")
    print("axis_1_2_primitive_projector_annihilations=verified")


if __name__ == "__main__":
    main()
