#!/usr/bin/env python3
"""Exact finite checks for Papadakis 2026 prime encodings.

This is a computational companion to
`InfoGeometry.Topology.PapadakisPrimes`.

It checks only finite arithmetic examples from the paper:
* Complete HPF-style outputs whose prime factors are forced beyond the base;
* the Goldbach product encoding example `L(C10)=3*7*13=273`.

It does not validate the paper's continuous harmonic limit claims.
"""

from __future__ import annotations

from dataclasses import dataclass

import sympy as sp


@dataclass(frozen=True)
class HPFExample:
    label: str
    value: int
    next_prime: int


def certify_hpf(example: HPFExample) -> None:
    factors = sorted(sp.factorint(example.value))
    assert example.value > 1, example
    assert example.value < example.next_prime**2, example
    assert all(p >= example.next_prime for p in factors), (example, factors)
    assert sp.isprime(example.value), example


def goldbach_encode(smalls: list[int], anchor_small: int, anchor_large: int) -> int:
    product = anchor_large * anchor_small
    for x in smalls:
        product *= x
    return product


def goldbach_recover(smalls: list[int], anchor_small: int, anchor_large: int) -> list[tuple[int, int]]:
    target = anchor_small + anchor_large
    return [(x, target - x) for x in smalls] + [(anchor_small, anchor_large)]


def main() -> None:
    examples = [
        HPFExample("5^2 - 2^2*3", 5**2 - 2**2 * 3, 7),
        HPFExample("3^3 - 2*5", 3**3 - 2 * 5, 7),
        HPFExample("2^2*3^2 - 5", 2**2 * 3**2 - 5, 7),
        HPFExample("2^2*3 + 5", 2**2 * 3 + 5, 7),
        HPFExample("2^3 + 3*5", 2**3 + 3 * 5, 7),
        HPFExample("165 - 14", 165 - 14, 13),
    ]
    for example in examples:
        certify_hpf(example)
        print(f"[HPF] {example.label} = {example.value} certified below {example.next_prime}^2")

    encoded = goldbach_encode([3], 7, 13)
    recovered = goldbach_recover([3], 7, 13)
    assert encoded == 273
    assert recovered == [(3, 17), (7, 13)]
    print("[Goldbach] L(C10)=273 recovers [(3, 17), (7, 13)]")


if __name__ == "__main__":
    main()
