#!/usr/bin/env python3
"""SymPy witness for the 2x2 determinant/KAN/Pauli chain."""

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
    a, b, c, d, th, al, n = sp.symbols("a b c d theta alpha n", real=True)
    M = sp.Matrix([[a, b], [c, d]])
    I = sp.eye(2)
    s3 = sp.Matrix([[1, 0], [0, -1]])
    sx = sp.Matrix([[0, 1], [1, 0]])
    is2 = sp.Matrix([[0, 1], [-1, 0]])

    det = a * d - b * c
    x, z, u, v = (a + d) / 2, (a - d) / 2, (b + c) / 2, (b - c) / 2
    assert_zero("det formula", M.det() - det)
    assert_zero("supertrace Tr(sigma3*M)=a-d", sp.trace(s3 * M) - (a - d))
    assert_zero("trace/traceless split", sp.trace(M - sp.trace(M) / 2 * I))
    assert_zero("Pauli reconstruction", M - (x * I + z * s3 + u * sx + v * is2))
    assert_zero("Pauli determinant", (x * I + z * s3 + u * sx + v * is2).det() - (x**2 - z**2 - u**2 + v**2))

    K = sp.Matrix([[sp.cos(th), -sp.sin(th)], [sp.sin(th), sp.cos(th)]])
    A = sp.Matrix([[sp.exp(al), 0], [0, sp.exp(-al)]])
    N = sp.Matrix([[1, n], [0, 1]])
    assert_zero("det K=1", K.det() - 1)
    assert_zero("det A=1", A.det() - 1)
    assert_zero("det N=1", N.det() - 1)
    assert_zero("det KAN=1", (K * A * N).det() - 1)

    klog = sp.Matrix([[0, -th], [th, 0]])
    alog = sp.Matrix([[al, 0], [0, -al]])
    nlog = sp.Matrix([[0, n], [0, 0]])
    assert_zero("tr kLog=0", sp.trace(klog))
    assert_zero("tr aLog=0", sp.trace(alog))
    assert_zero("tr nLog=0", sp.trace(nlog))
    print("OK matrix2 KAN/Pauli chain SymPy witness completed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
