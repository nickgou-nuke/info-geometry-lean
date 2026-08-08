#!/usr/bin/env python3
"""Graded natural generator basis for O(5,5).

For eta = diag(+1^5, -1^5), a natural basis element for coordinates i<j is

    M_ij = E_ij - s_i s_j E_ji

where s_i is the eta sign.  If the signs match, this is a compact rotation
generator.  If the signs differ, this is a mixed boost generator.

The script verifies the full 45-generator o(5,5) basis and the 15-generator
active basis left after freezing coordinates 0..3.
"""

from __future__ import annotations

import numpy as np

from frozen_pin55_manifold_flow import eta55, o55_residual


def signs55() -> np.ndarray:
    return np.array([1.0] * 5 + [-1.0] * 5)


def generator(i: int, j: int, signs: np.ndarray) -> np.ndarray:
    if not i < j:
        raise ValueError("expected i < j")
    matrix = np.zeros((10, 10))
    matrix[i, j] = 1.0
    matrix[j, i] = -signs[i] * signs[j]
    return matrix


def grade(i: int, j: int, signs: np.ndarray) -> str:
    if signs[i] > 0 and signs[j] > 0:
        return "positive_rotation"
    if signs[i] < 0 and signs[j] < 0:
        return "negative_rotation"
    return "mixed_boost"


def basis(indices: list[int]) -> list[tuple[str, int, int, np.ndarray]]:
    signs = signs55()
    out = []
    for pos, i in enumerate(indices):
        for j in indices[pos + 1:]:
            out.append((grade(i, j, signs), i, j, generator(i, j, signs)))
    return out


def grade_counts(items: list[tuple[str, int, int, np.ndarray]]) -> dict[str, int]:
    counts = {"positive_rotation": 0, "negative_rotation": 0, "mixed_boost": 0}
    for item in items:
        counts[item[0]] += 1
    return counts


def max_residual(items: list[tuple[str, int, int, np.ndarray]]) -> float:
    eta = eta55()
    return max(o55_residual(item[3], eta) for item in items)


def linear_combination(items: list[tuple[str, int, int, np.ndarray]]) -> np.ndarray:
    coeffs = np.linspace(0.01, 0.01 * len(items), len(items))
    combo = np.zeros((10, 10))
    for coeff, item in zip(coeffs, items):
        combo += coeff * item[3]
    return combo


def main() -> None:
    full = basis(list(range(10)))
    active = basis(list(range(4, 10)))
    full_counts = grade_counts(full)
    active_counts = grade_counts(active)

    full_combo = linear_combination(full)
    active_combo = linear_combination(active)

    print("full basis count =", len(full))
    print("full grade counts =", full_counts)
    print("active basis count =", len(active))
    print("active grade counts =", active_counts)
    print("full max o(5,5) residual =", f"{max_residual(full):.3e}")
    print("active max o(5,5) residual =", f"{max_residual(active):.3e}")
    print("full combo residual =", f"{o55_residual(full_combo, eta55()):.3e}")
    print("active combo residual =", f"{o55_residual(active_combo, eta55()):.3e}")

    assert len(full) == 45
    assert full_counts == {
        "positive_rotation": 10,
        "negative_rotation": 10,
        "mixed_boost": 25,
    }
    assert len(active) == 15
    assert active_counts == {
        "positive_rotation": 0,
        "negative_rotation": 10,
        "mixed_boost": 5,
    }
    assert max_residual(full) == 0.0
    assert max_residual(active) == 0.0
    assert o55_residual(full_combo, eta55()) < 1e-12
    assert o55_residual(active_combo, eta55()) < 1e-12
    print("o55_graded_generator_basis.py: graded O(5,5) basis audit passed")


if __name__ == "__main__":
    main()
