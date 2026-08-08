#!/usr/bin/env python3
"""SymPy witness for two-port scattering coefficients.

For S=[[t,rL],[rR,t]] and J=diag(1,-1), checks:
  S.T J S = [[t^2-rR^2, t(rL-rR)], [t(rL-rR), rL^2-t^2]]
  D = S.T S - I
and verifies the hyperbolic chip specialization t=cosh(a), rL=rR=sinh(a).
"""

from __future__ import annotations

import sympy as sp


def assert_zero(name: str, expr) -> None:
    if isinstance(expr, sp.MatrixBase):
        residue = expr.applyfunc(sp.simplify)
        ok = residue == sp.zeros(*residue.shape)
    else:
        residue = sp.simplify(expr)
        ok = residue == 0
    print(f"{name}: {'PASS' if ok else 'FAIL'}")
    if not ok:
        print(residue)
        raise SystemExit(1)


def main() -> int:
    t, rL, rR, a = sp.symbols("t rL rR alpha", real=True)
    S = sp.Matrix([[t, rL], [rR, t]])
    J = sp.diag(1, -1)
    I2 = sp.eye(2)

    junitary_matrix = S.T * J * S
    expected_j = sp.Matrix([[t**2 - rR**2, t * rL - rR * t], [rL * t - t * rR, rL**2 - t**2]])
    assert_zero("two-port J-unitarity matrix formula", junitary_matrix - expected_j)

    defect = S.T * S - I2
    expected_defect = sp.Matrix([[t**2 + rR**2 - 1, t * rL + rR * t], [rL * t + t * rR, rL**2 + t**2 - 1]])
    assert_zero("two-port Euclidean defect formula", defect - expected_defect)

    Sh = sp.Matrix([[sp.cosh(a), sp.sinh(a)], [sp.sinh(a), sp.cosh(a)]])
    assert_zero("hyperbolic two-port S.T*J*S=J", Sh.T * J * Sh - J)
    assert_zero("hyperbolic T-R=1", sp.cosh(a) ** 2 - sp.sinh(a) ** 2 - 1)
    assert_zero("hyperbolic Euclidean defect scalar=2sinh^2", (sp.cosh(a) ** 2 + sp.sinh(a) ** 2 - 1) - 2 * sp.sinh(a) ** 2)

    print("OK two-port scattering coefficients SymPy witness completed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
