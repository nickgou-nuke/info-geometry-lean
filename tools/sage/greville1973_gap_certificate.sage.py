#!/usr/bin/env sage -python
"""
GAP-through-Sage exact-rational certificate for Greville 1973 Souriau--Frame /
Drazin packet.

This uses Sage's libgap bridge to verify the same finite exact-rational packet in
GAP syntax, so the external lane is checked independently of the pure Sage and
SymPy certificates.
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
    print("=== Greville 1973 GAP/Sage certificate ===")

    libgap.eval('AA := [[0,1,0],[0,0,0],[0,0,2]]')
    libgap.eval('II := IdentityMat(3, Rationals)')
    libgap.eval('p1 := TraceMat(AA * II)')
    libgap.eval('B1 := AA * II - p1 * II')
    libgap.eval('p2 := (1/2) * TraceMat(AA * B1)')
    libgap.eval('B2 := AA * B1 - p2 * II')
    libgap.eval('p3 := (1/3) * TraceMat(AA * B2)')
    libgap.eval('B3 := AA * B2 - p3 * II')

    require('p1 = 2', 'p1 = 2')
    require('p2 = 0', 'p2 = 0')
    require('p3 = 0', 'p3 = 0')
    require('B3 = NullMat(3,3,Rationals)', 'B3 = 0')
    print('PASS: Souriau-Frame recurrence has r=3, s=1, k=2')

    libgap.eval('XX := (1/(p1^3)) * (AA^2) * (II^3)')
    libgap.eval('Expected := [[0,0,0],[0,0,0],[0,0,1/2]]')
    require('XX = Expected', 'Greville formula gives expected Drazin inverse')
    require('AA * XX = XX * AA', 'A X = X A')
    require('XX * AA * XX = XX', 'X A X = X')
    require('AA^3 * XX = AA^2', 'A^(k+1) X = A^k for k=2')
    require('AA * XX * XX = XX', 'A X^2 = X')
    print('PASS: Drazin index-2 equations hold')

    libgap.eval('Regular := AA * XX')
    libgap.eval('Nilpotent := II - Regular')
    require('Regular = [[0,0,0],[0,0,0],[0,0,1]]', 'regular projector')
    require('Nilpotent = [[1,0,0],[0,1,0],[0,0,0]]', 'nilpotent projector')
    require('Regular * Regular = Regular', 'regular idempotent')
    require('Nilpotent * Nilpotent = Nilpotent', 'nilpotent idempotent')
    require('(AA * Nilpotent)^2 = NullMat(3,3,Rationals)', 'nilpotent lane square-zero')
    print('PASS: Drazin projectors split regular and nilpotent lanes')

    libgap.eval('PP := [[0,0,1],[0,1,0],[1,0,0]]')
    libgap.eval('PPinv := Inverse(PP)')
    libgap.eval('Ac := PP * AA * PPinv')
    libgap.eval('Xc := PP * XX * PPinv')
    require('Ac * Xc = Xc * Ac', 'conjugated commutation')
    require('Xc * Ac * Xc = Xc', 'conjugated X A X = X')
    require('Ac^3 * Xc = Ac^2', 'conjugated Drazin power law')
    print('PASS: GL_3(Q) conjugation preserves the Drazin packet')

    print('GREVILLE1973_GAP_SAGE_CERTIFICATE_OK')


if __name__ == '__main__':
    main()
