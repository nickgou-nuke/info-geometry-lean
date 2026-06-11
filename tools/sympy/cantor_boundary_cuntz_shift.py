#!/usr/bin/env python3
"""Finite witness for Cantor boundary Cuntz shift conventions.

The Lean owner is
`InfoGeometry.Canonical.CantorBoundaryCuntzShift`.

This script verifies the finite/cylindrical mechanics:
1. front-prefix maps for symbolic Cuntz left/right branches;
2. stage-local append maps compatible with the UHF diagonal successor embedding;
3. a downstream finite CAR matrix witness.

It deliberately does not construct a finite-dimensional representation of the
unital Cuntz algebra O_2.
"""

from __future__ import annotations

import sympy as sp


def prefix_bit(bit: bool, stream: tuple[bool, ...]) -> tuple[bool, ...]:
    return (bit,) + stream[:-1]


def boundary_prefix(n: int, stream: tuple[bool, ...]) -> tuple[bool, ...]:
    return stream[:n]


def append_bit_at_depth(n: int, bit: bool, stream: tuple[bool, ...]) -> tuple[bool, ...]:
    out = list(stream)
    out[n] = bit
    return tuple(out)


def prefix_succ(word: tuple[bool, ...]) -> tuple[bool, ...]:
    return word[:-1]


def extend_succ(word: tuple[bool, ...], bit: bool) -> tuple[bool, ...]:
    return word + (bit,)


def diag_embed_succ(f):
    return lambda word: f(prefix_succ(word))


def cylinder(n: int, f, stream: tuple[bool, ...]):
    return f(boundary_prefix(n, stream))


def main() -> None:
    print("=== CANTOR BOUNDARY CUNTZ SHIFT WITNESS ===")

    stream = (True, False, True, True, False, False)

    left = prefix_bit(False, stream)
    right = prefix_bit(True, stream)
    assert left[0] is False
    assert right[0] is True
    assert left[1:] == stream[:-1]
    assert right[1:] == stream[:-1]
    print("[1] front-prefix symbolic left/right branch laws verified")

    n = 3
    f = lambda word: sum((2**i if bit else 0) for i, bit in enumerate(word))

    for bit in (False, True):
        appended = append_bit_at_depth(n, bit, stream)
        assert boundary_prefix(n + 1, appended) == extend_succ(boundary_prefix(n, stream), bit)
        lhs = cylinder(n + 1, diag_embed_succ(f), appended)
        rhs = cylinder(n, f, stream)
        assert lhs == rhs

    print("[2] stage-local append laws and UHF cylinder compatibility verified")

    a = sp.Matrix([[0, 1], [0, 0]])
    astar = a.T
    assert a * a == sp.zeros(2)
    assert a * astar + astar * a == sp.eye(2)
    print("[3] downstream finite CAR matrix witness verified")

    print("=== SUCCESS: OPERATOR ALGEBRA FIRST, TOPOLOGY LATER ===")


if __name__ == "__main__":
    main()

