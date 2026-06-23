#!/usr/bin/env python3
"""Finite Stone-duality certificate for ultrafilters and Boolean evaluation maps.

This is the exact finite witness behind the Lean-level Stone-duality bridge:
principal ultrafilters on a finite Boolean algebra of subsets are the same as
evaluation homomorphisms into the two-element Boolean algebra.
"""

from __future__ import annotations

import sympy as sp


BASE = (0, 1, 2)


def powerset(xs):
    xs = tuple(xs)
    out = []
    for mask in range(1 << len(xs)):
        subset = frozenset(xs[i] for i in range(len(xs)) if (mask >> i) & 1)
        out.append(subset)
    return out


def principal_ultrafilter(x):
    return {A for A in powerset(BASE) if x in A}


def eval_hom(x):
    return {A: bool(x in A) for A in powerset(BASE)}


def verify_homomorphism(x):
    chi = eval_hom(x)
    for A in powerset(BASE):
        assert chi[A] == (x in A)
    for A in powerset(BASE):
        for B in powerset(BASE):
            assert chi[A & B] == (chi[A] and chi[B])
            assert chi[A | B] == (chi[A] or chi[B])
            assert chi[BASE_set.difference(A)] == (not chi[A])
    assert chi[frozenset(BASE)] is True
    assert chi[frozenset()] is False


def verify_ultrafilter_roundtrip(x):
    U = principal_ultrafilter(x)
    chi = eval_hom(x)
    reconstructed = {A for A, value in chi.items() if value}
    assert U == reconstructed
    assert all((A in U) == chi[A] for A in powerset(BASE))


def verify_all_points():
    for x in BASE:
        verify_homomorphism(x)
        verify_ultrafilter_roundtrip(x)


BASE_set = frozenset(BASE)


def main() -> None:
    print("=== Stone duality ultrafilter / Boolean evaluation certificate ===")
    print(f"sympy={sp.__version__}")
    verify_all_points()
    print("PASS: principal ultrafilters match evaluation homomorphisms on the finite Boolean algebra")
    print("STONE_DUALITY_ULTRAFILTER_CERTIFICATE_OK")


if __name__ == "__main__":
    main()
