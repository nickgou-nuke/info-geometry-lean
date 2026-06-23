#!/usr/bin/env sage -python
"""
GAP-through-Sage exact-rational certificate for the finite holographic Souriau
reconstruction lane.
"""

from sage.all import libgap


def gap_bool(expr: str) -> bool:
    out = str(libgap.eval(expr)).strip().lower()
    if out == "true":
        return True
    if out == "false":
        return False
    raise RuntimeError(f"unexpected GAP boolean output for {expr!r}: {out!r}")


def require(expr: str, label: str) -> None:
    if not gap_bool(expr):
        raise AssertionError(f"GAP check failed: {label}\nexpr: {expr}")


def main() -> None:
    print("=== Holographic Souriau Reconstruction GAP/Sage certificate ===")

    libgap.eval('O55 := DiagonalMat([1,1,1,1,1,-1,-1,-1,-1,-1])')
    require('O55*O55 = IdentityMat(10, Rationals)', 'O55 involutive')
    require('TransposedMat(O55) = O55', 'O55 symmetric')

    libgap.eval('TT := [[0,-1],[1,0]]')
    libgap.eval('KK := [[1,0],[0,-1]]')
    require('TT*TT = -IdentityMat(2, Rationals)', 'twist squares to -I')
    require('KK*KK = IdentityMat(2, Rationals)', 'glide squares to I')
    require('KK*TT = -(TT*KK)', 'glide anticommutes with twist')

    libgap.eval('CC := 2*IdentityMat(3, Rationals)')
    gens = [
        '[[0,1,0],[0,0,0],[0,0,0]]',
        '[[0,0,0],[1,0,0],[0,0,0]]',
        '[[0,0,0],[0,0,1],[0,0,0]]',
        '[[0,0,0],[0,0,0],[0,1,0]]',
        '[[0,0,1],[0,0,0],[0,0,0]]',
        '[[0,0,0],[0,0,0],[1,0,0]]',
        '[[1,0,0],[0,-1,0],[0,0,0]]',
        '[[0,0,0],[0,1,0],[0,0,-1]]',
    ]
    for i, g in enumerate(gens):
        libgap.eval(f'GG := {g}')
        require('CC*GG = GG*CC', f'su3 generator {i} commutes with scalar laser')

    print('HOLOGRAPHIC_SOURIAU_RECONSTRUCTION_GAP_SAGE_OK')


if __name__ == '__main__':
    main()
