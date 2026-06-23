#!/usr/bin/env python3
"""Symbolic twin for the finite Cantor/split-null bridge.

This mirrors only the finite theorem-safe packet:
- two explicit split-Zorn null generators;
- square-zero and self-polar-zero checks;
- cross-polar hyperbolic pairing;
- a finite address map sending the last Cantor branch bit to one of the two
  isotropic generators.

No global colimit, GNS-quotient, or exceptional-group closure theorem is
claimed here.
"""

from __future__ import annotations

import sympy as sp


def det_z(z):
    r, s, x1, x2, x3, y1, y2, y3 = z
    return sp.expand(r * s - (x1 * y1 + x2 * y2 + x3 * y3))


def add_z(x, y):
    return tuple(sp.expand(a + b) for a, b in zip(x, y, strict=True))


def mul_z(x, y):
    r, s, x1, x2, x3, y1, y2, y3 = x
    R, S, u1, u2, u3, v1, v2, v3 = y
    return (
        sp.expand(r * R + (x1 * v1 + x2 * v2 + x3 * v3)),
        sp.expand((y1 * u1 + y2 * u2 + y3 * u3) + s * S),
        sp.expand(r * u1 + S * x1 - (y2 * v3 - y3 * v2)),
        sp.expand(r * u2 + S * x2 - (y3 * v1 - y1 * v3)),
        sp.expand(r * u3 + S * x3 - (y1 * v2 - y2 * v1)),
        sp.expand(R * y1 + s * v1 + (x2 * u3 - x3 * u2)),
        sp.expand(R * y2 + s * v2 + (x3 * u1 - x1 * u3)),
        sp.expand(R * y3 + s * v3 + (x1 * u2 - x2 * u1)),
    )


def polar_z(x, y):
    return sp.expand(det_z(add_z(x, y)) - det_z(x) - det_z(y))


def bit_null_generator(bit: bool):
    top_right = (0, 0, 1, 0, 0, 0, 0, 0)
    bottom_left = (0, 0, 0, 0, 0, 1, 0, 0)
    return bottom_left if bit else top_right


def address_null_generator(word: list[bool]):
    zero = (0, 0, 0, 0, 0, 0, 0, 0)
    return zero if not word else bit_null_generator(word[-1])


def main() -> None:
    top_right = bit_null_generator(False)
    bottom_left = bit_null_generator(True)
    zero = (0, 0, 0, 0, 0, 0, 0, 0)

    assert det_z(top_right) == 0
    assert det_z(bottom_left) == 0
    assert top_right != zero
    assert bottom_left != zero
    assert mul_z(top_right, top_right) == zero
    assert mul_z(bottom_left, bottom_left) == zero
    assert polar_z(top_right, top_right) == 0
    assert polar_z(bottom_left, bottom_left) == 0
    assert polar_z(top_right, bottom_left) == -1

    sample_words = [[], [False], [True], [True, False], [False, True]]
    expected = [zero, top_right, bottom_left, top_right, bottom_left]
    assert [address_null_generator(w) for w in sample_words] == expected

    print("cantor_split_null_bridge: symbolic checks passed")
    print(f"cross-polar(topRight,bottomLeft) = {polar_z(top_right, bottom_left)}")


if __name__ == "__main__":
    main()
