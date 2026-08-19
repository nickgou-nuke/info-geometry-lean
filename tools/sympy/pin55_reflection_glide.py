#!/usr/bin/env python3
"""SymPy twin for `InfoGeometry.Clifford.Pin55ReflectionGlide`.

Verified here:
- a first-pair sign reflection preserves the split O(5,5) hyperbolic pairing;
- the reflection is involutive;
- reflection plus a half-translation along an invariant coordinate is a glide
  whose square is a unit translation.

Not verified here:
- a full Clifford algebra representation of Pin(5,5);
- the double-cover map Pin(5,5) -> O(5,5);
- any physical spacetime theorem.
"""

from __future__ import annotations

import sympy as sp


def split_pair(x: sp.Matrix, y: sp.Matrix) -> sp.Expr:
    n = 5
    return sum(x[i] * y[n + i] + x[n + i] * y[i] for i in range(n))


def pin_reflection_matrix() -> sp.Matrix:
    r = sp.eye(10)
    r[0, 0] = -1
    r[5, 5] = -1
    return r


def translate_invariant(x: sp.Matrix, amount: sp.Expr) -> sp.Matrix:
    y = sp.Matrix(x)
    y[1] += amount
    return y


def glide(x: sp.Matrix) -> sp.Matrix:
    return translate_invariant(pin_reflection_matrix() * x, sp.Rational(1, 2))


def main() -> None:
    print("--- SymPy Twin: finite Pin(5,5) reflection/glide interface ---")

    x_symbols = sp.symbols("x0:10")
    y_symbols = sp.symbols("y0:10")
    x = sp.Matrix(x_symbols)
    y = sp.Matrix(y_symbols)
    reflection = pin_reflection_matrix()

    assert sp.simplify(split_pair(reflection * x, reflection * y) - split_pair(x, y)) == 0
    print("reflection preserves split O(5,5) pairing: OK")

    assert reflection * reflection == sp.eye(10)
    print("reflection is involutive: OK")

    glide_squared = sp.simplify(glide(glide(x)))
    unit_translation = translate_invariant(x, 1)
    assert glide_squared == unit_translation
    print("glide squared equals unit translation: OK")

    print("[SUCCESS] finite Pin(5,5)-style reflection/glide identities verified.")


if __name__ == "__main__":
    main()
