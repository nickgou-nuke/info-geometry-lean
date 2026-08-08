#!/usr/bin/env python3
"""SymPy witness for optical Andreev/Jones spinor algebra."""

from __future__ import annotations

import sympy as sp


def assert_zero(name: str, expr) -> None:
    residue = expr.applyfunc(sp.simplify) if isinstance(expr, sp.MatrixBase) else sp.simplify(expr)
    ok = residue == sp.zeros(*residue.shape) if isinstance(residue, sp.MatrixBase) else residue == 0
    print(f"{name}: {'PASS' if ok else 'FAIL'}")
    if not ok:
        print(residue)
        raise SystemExit(1)


def main() -> int:
    I = sp.I
    R = sp.Matrix([1, I])
    L = sp.Matrix([1, -I])
    i_sigma2 = sp.Matrix([[0, 1], [-1, 0]])

    def conj(v: sp.Matrix) -> sp.Matrix:
        return v.applyfunc(sp.conjugate)

    assert_zero("conj(R)=L", conj(R) - L)
    assert_zero("conj(L)=R", conj(L) - R)
    assert_zero("T(R)=(-i)L", i_sigma2 * conj(R) - (-I) * L)
    assert_zero("T(L)=iR", i_sigma2 * conj(L) - I * R)

    hwp = sp.diag(-I, I)
    assert_zero("HWP*R=(-i)L", hwp * R - (-I) * L)
    assert_zero("HWP*L=(-i)R", hwp * L - (-I) * R)
    assert_zero("det(HWP)=1", sp.det(hwp) - 1)

    alpha = sp.symbols("alpha", real=True)
    dichroic_boost = sp.diag(sp.exp(alpha), sp.exp(-alpha))
    assert_zero("det Jones dichroic boost=1", sp.det(dichroic_boost) - 1)

    total_s3 = sp.diag(2, 0, 0, -2)
    singlet = sp.Matrix([0, 1, -1, 0])
    assert_zero("singlet total sigma3 spin zero", total_s3 * singlet)

    chi, s3 = sp.symbols("chi s3", real=True)
    sigma3 = sp.diag(1, -1)
    Hax = chi * s3 * sigma3
    assert_zero("Tr(chi*S3*sigma3)=0", sp.trace(Hax))
    G = sp.diag(sp.exp(chi * s3), sp.exp(-chi * s3))
    assert_zero("det nonlinear axial gate=1", sp.det(G) - 1)

    print("OK optical Andreev spinor SymPy witness completed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
