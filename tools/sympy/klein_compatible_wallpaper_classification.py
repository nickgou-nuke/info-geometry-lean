"""Exact-rational certificate for finite Klein-compatible wallpaper candidates.

This script mirrors
`InfoGeometry.Topology.KleinCompatibleWallpaperClassification`.

It proves only the finite affine/cross-section facts:

* the nonzero projection of the `D5` root system to the first two coordinates is
  `{±e1, ±e2, ±(e1-e2), ±(e1+e2)}`;
* the `pg`, `pmg`, and `pgg` finite affine representatives carry local Klein
  glide corridors;
* the representative normals used by those corridors lie in that projected
  `D5` root cross-section.

It does not classify all crystallographic wallpaper groups.
"""

from __future__ import annotations

import sympy as sp


QQ = sp.Rational


def mat(rows: list[list[object]]) -> sp.Matrix:
    return sp.Matrix([[QQ(x) for x in row] for row in rows])


def key(v: sp.Matrix) -> tuple[sp.Rational, ...]:
    return tuple(sp.Rational(v[i, 0]) for i in range(v.rows))


def d5_roots() -> list[sp.Matrix]:
    roots: list[sp.Matrix] = []
    for i in range(5):
        for j in range(i + 1, 5):
            for si in (QQ(1), QQ(-1)):
                for sj in (QQ(1), QQ(-1)):
                    v = [QQ(0)] * 5
                    v[i] = si
                    v[j] = sj
                    roots.append(sp.Matrix(v))
    return roots


def project2(v: sp.Matrix) -> sp.Matrix:
    return sp.Matrix([v[0, 0], v[1, 0]])


def projected_d5_roots() -> set[tuple[sp.Rational, sp.Rational]]:
    roots = d5_roots()
    projected = {key(project2(r)) for r in roots}
    projected.discard((QQ(0), QQ(0)))
    return projected


def inv_affine(M: sp.Matrix) -> sp.Matrix:
    return M.inv()


def verify_affine_candidates(projected: set[tuple[sp.Rational, sp.Rational]]) -> None:
    I = sp.eye(3)
    Tx = mat([[1, 0, 1], [0, 1, 0], [0, 0, 1]])
    Ty = mat([[1, 0, 0], [0, 1, 1], [0, 0, 1]])
    Gx = mat([[1, 0, QQ(1, 2)], [0, -1, 0], [0, 0, 1]])
    mirror_x = mat([[-1, 0, 0], [0, 1, 0], [0, 0, 1]])
    Gy = mat([[-1, 0, 0], [0, 1, QQ(1, 2)], [0, 0, 1]])

    assert Gx * Gx == Tx
    assert Gx * Ty == inv_affine(Ty) * Gx
    print("PASS: pg finite affine corridor")

    assert mirror_x * mirror_x == I
    assert Gx * Gx == Tx
    assert Gx * Ty == inv_affine(Ty) * Gx
    print("PASS: pmg finite representative corridor")

    assert Gy * Gy == Ty
    assert Gy * Tx == inv_affine(Tx) * Gy
    assert Gx * Ty == inv_affine(Ty) * Gx
    print("PASS: pgg finite two-glide corridor")

    candidate_normals = {
        "pg": [(QQ(0), QQ(1)), (QQ(1), QQ(-1))],
        "pmg": [(QQ(1), QQ(0)), (QQ(0), QQ(1))],
        "pgg": [(QQ(1), QQ(0)), (QQ(0), QQ(1))],
    }
    for name, normals in candidate_normals.items():
        for normal in normals:
            assert normal in projected
        print(f"PASS: {name} normals lie in projected D5 cross-section")


def main() -> None:
    print("=== Klein-compatible wallpaper classification SymPy certificate ===")
    roots = d5_roots()
    assert len(roots) == 40
    projected = projected_d5_roots()
    expected = {
        (QQ(-1), QQ(-1)),
        (QQ(-1), QQ(0)),
        (QQ(-1), QQ(1)),
        (QQ(0), QQ(-1)),
        (QQ(0), QQ(1)),
        (QQ(1), QQ(-1)),
        (QQ(1), QQ(0)),
        (QQ(1), QQ(1)),
    }
    assert projected == expected
    print("PASS: nonzero D5 projection is B2/C2 eight-root set")

    unoriented = {
        tuple(v)
        for v in ((QQ(1), QQ(1)), (QQ(1), QQ(0)), (QQ(1), QQ(-1)), (QQ(0), QQ(1)))
    }
    assert unoriented.issubset(projected | {(-a, -b) for (a, b) in projected})
    print("PASS: unoriented directions e1, e2, e1-e2, e1+e2")

    verify_affine_candidates(projected)
    print("KLEIN_COMPATIBLE_WALLPAPER_CLASSIFICATION_SYMPY_CERTIFICATE_OK")


if __name__ == "__main__":
    main()
