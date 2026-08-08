#!/usr/bin/env python3
"""SymPy witness: KAN transfer matrix -> connection -> scattering matrix."""

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
    k, a, g = sp.symbols("k alpha gamma", real=True)
    K = sp.Matrix([[sp.cos(k), -sp.sin(k)], [sp.sin(k), sp.cos(k)]])
    A = sp.diag(sp.exp(a), sp.exp(-a))
    N = sp.Matrix([[1, g], [0, 1]])
    M = sp.simplify(K * A * N)

    expected_M = sp.Matrix([
        [sp.exp(a) * sp.cos(k), g * sp.exp(a) * sp.cos(k) - sp.exp(-a) * sp.sin(k)],
        [sp.exp(a) * sp.sin(k), g * sp.exp(a) * sp.sin(k) + sp.exp(-a) * sp.cos(k)],
    ])
    assert_zero("KAN transfer matrix formula", M - expected_M)
    assert_zero("det M=1", sp.det(M) - 1)

    Ak = sp.simplify(M.inv() * sp.diff(M, k))
    expected_Ak = sp.Matrix([
        [-g * sp.exp(2*a), -(g**2 * sp.exp(4*a) + 1) * sp.exp(-2*a)],
        [sp.exp(2*a), g * sp.exp(2*a)],
    ])
    assert_zero("connection formula", Ak - expected_Ak)
    assert_zero("Tr(A_k)=0", sp.trace(Ak))

    m11, m12, m21, m22 = M[0, 0], M[0, 1], M[1, 0], M[1, 1]
    S = sp.simplify((1 / m22) * sp.Matrix([[1, -m12], [m21, sp.det(M)]]))
    assert_zero("reciprocal transmission", S[0, 0] - S[1, 1])
    print("S(k,alpha,gamma)=")
    sp.pprint(S)
    print("OK transfer matrix scattering SymPy witness completed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
