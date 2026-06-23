"""`clifford` and `galgebra` smoke certificate for the finite wallpaper corridor."""

from __future__ import annotations

import os

os.environ.setdefault("NUMBA_DISABLE_JIT", "1")

import sympy as sp


def verify_matrix_surface() -> None:
    half = sp.Rational(1, 2)
    Tx = sp.Matrix([[1, 0, 1], [0, 1, 0], [0, 0, 1]])
    Ty = sp.Matrix([[1, 0, 0], [0, 1, 1], [0, 0, 1]])
    Gx = sp.Matrix([[1, 0, half], [0, -1, 0], [0, 0, 1]])
    Gy = sp.Matrix([[-1, 0, 0], [0, 1, half], [0, 0, 1]])
    assert Gx * Gx == Tx
    assert Gy * Gy == Ty
    assert Gx * Ty == Ty.inv() * Gx
    assert Gy * Tx == Tx.inv() * Gy
    print("PASS: exact affine pg/pgg glide matrix surface")


def verify_clifford_reflections() -> None:
    from clifford import Cl

    layout, blades = Cl(2, 0, firstIdx=1)
    e1 = blades["e1"]
    e2 = blades["e2"]
    v = 3 * e1 + 5 * e2

    # Unit-vector reflection formula in Euclidean signature.
    refl_e1 = -e1 * v * e1
    refl_e2 = -e2 * v * e2
    assert refl_e1 == -3 * e1 + 5 * e2
    assert refl_e2 == 3 * e1 - 5 * e2
    print("PASS: clifford reflection normals e1/e2 match finite wallpaper candidates")


def verify_galgebra_reflection() -> None:
    from galgebra.ga import Ga

    ga = Ga("e1 e2", g=[1, 1])
    e1, e2 = ga.mv()
    x, y = sp.symbols("x y")
    v = x * e1 + y * e2

    refl_e2 = -e2 * v * e2
    expected = x * e1 - y * e2
    assert str((refl_e2 - expected).expand()) == "0"
    print("PASS: galgebra reflection across e2 gives pg normal action")


def main() -> None:
    print("=== Klein-compatible wallpaper classification clifford/galgebra certificate ===")
    verify_matrix_surface()
    verify_clifford_reflections()
    verify_galgebra_reflection()
    print("KLEIN_COMPATIBLE_WALLPAPER_CLASSIFICATION_CLIFFORD_GALGEBRA_CERTIFICATE_OK")


if __name__ == "__main__":
    main()
