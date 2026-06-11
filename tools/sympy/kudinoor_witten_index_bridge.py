#!/usr/bin/env python3
"""
Finite Kudinoor supersymmetry/Witten-index bridge witness.

This mirrors lean/InfoGeometry/Arithmetic/KudinoorWittenIndexBridge.lean.
It verifies only the finite graded-spectrum cancellation: paired nonzero
energy levels do not contribute to the weighted supertrace, so the result is
the zero-energy Witten index and is independent of nonzero-level weights.
"""

from __future__ import annotations

import sympy as sp


def level_superdimension(boson: dict[str, int], fermion: dict[str, int], level: str) -> int:
    return boson[level] - fermion[level]


def finite_witten_index(
    levels: list[str],
    zero_levels: set[str],
    boson: dict[str, int],
    fermion: dict[str, int],
) -> int:
    return sum(level_superdimension(boson, fermion, level) for level in levels if level in zero_levels)


def finite_weighted_supertrace(
    levels: list[str],
    boson: dict[str, int],
    fermion: dict[str, int],
    weight: dict[str, sp.Expr],
) -> sp.Expr:
    return sp.simplify(
        sum(level_superdimension(boson, fermion, level) * weight[level] for level in levels)
    )


def main() -> None:
    print("=" * 72)
    print("KUDINOOR WITTEN INDEX BRIDGE -- SYMPY VERIFICATION")
    print("=" * 72)

    levels = ["E0a", "E0b", "E1", "E2", "E3"]
    zero_levels = {"E0a", "E0b"}

    boson = {
        "E0a": 3,
        "E0b": 1,
        "E1": 5,
        "E2": 2,
        "E3": 4,
    }
    fermion = {
        "E0a": 1,
        "E0b": 2,
        "E1": 5,
        "E2": 2,
        "E3": 4,
    }

    beta, gamma = sp.symbols("beta gamma", positive=True)
    weight_beta = {
        "E0a": 1,
        "E0b": 1,
        "E1": sp.exp(-beta),
        "E2": sp.exp(-2 * beta),
        "E3": sp.exp(-3 * beta),
    }
    weight_gamma = {
        "E0a": 1,
        "E0b": 1,
        "E1": sp.exp(-gamma),
        "E2": sp.exp(-5 * gamma),
        "E3": sp.Rational(7, 11),
    }

    for level in levels:
        if level not in zero_levels:
            if boson[level] != fermion[level]:
                raise AssertionError(f"nonzero level {level} is not paired")
        else:
            if weight_beta[level] != 1 or weight_gamma[level] != 1:
                raise AssertionError(f"zero level {level} is not normalized")

    index = finite_witten_index(levels, zero_levels, boson, fermion)
    supertrace_beta = finite_weighted_supertrace(levels, boson, fermion, weight_beta)
    supertrace_gamma = finite_weighted_supertrace(levels, boson, fermion, weight_gamma)

    if sp.simplify(supertrace_beta - index) != 0:
        raise AssertionError("beta supertrace does not collapse to Witten index")
    if sp.simplify(supertrace_gamma - index) != 0:
        raise AssertionError("gamma supertrace does not collapse to Witten index")
    if sp.simplify(supertrace_beta - supertrace_gamma) != 0:
        raise AssertionError("weighted supertrace is not weight-independent")

    print(f"  finite Witten index: {index}")
    print("  paired nonzero levels cancel from weighted supertrace")
    print("  changing nonzero weights leaves the supertrace unchanged")
    print("=" * 72)
    print("KUDINOOR WITTEN INDEX BRIDGE VERIFIED")
    print("=" * 72)


if __name__ == "__main__":
    main()
