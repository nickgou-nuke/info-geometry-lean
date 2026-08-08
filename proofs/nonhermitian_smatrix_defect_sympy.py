#!/usr/bin/env python3
"""SymPy witness for the non-Hermitian hyperbolic S-matrix defect.

S(a) = cosh(a) I + sinh(a) P, P = sigma_x.
Checks:
- parity-twisted supertrace Tr(P S) = 2 sinh(a);
- det S = 1;
- Euclidean defect S.T S - I;
- Krein/J flux preservation S.T J S = J.
"""

from __future__ import annotations

import sympy as sp


def assert_zero(name: str, expr) -> None:
    residue = sp.simplify(expr)
    if isinstance(residue, sp.MatrixBase):
        residue = residue.applyfunc(sp.simplify)
        ok = residue == sp.zeros(*residue.shape)
    else:
        ok = residue == 0
    print(f"{name}: {'PASS' if ok else 'FAIL'}")
    if not ok:
        print(residue)
        raise SystemExit(1)


def main() -> int:
    a = sp.symbols("alpha", real=True)
    I2 = sp.eye(2)
    P = sp.Matrix([[0, 1], [1, 0]])
    J = sp.diag(1, -1)
    S = sp.cosh(a) * I2 + sp.sinh(a) * P

    assert_zero("S explicit", S - sp.Matrix([[sp.cosh(a), sp.sinh(a)], [sp.sinh(a), sp.cosh(a)]]))
    assert_zero("Tr(P*S)=2*sinh(alpha)", sp.trace(P * S) - 2 * sp.sinh(a))
    assert_zero("det(S)=1", sp.det(S) - 1)

    defect = S.T * S - I2
    expected_defect = sp.Matrix(
        [
            [sp.cosh(a) ** 2 + sp.sinh(a) ** 2 - 1, 2 * sp.sinh(a) * sp.cosh(a)],
            [2 * sp.sinh(a) * sp.cosh(a), sp.cosh(a) ** 2 + sp.sinh(a) ** 2 - 1],
        ]
    )
    assert_zero("Euclidean nonunitary defect formula", defect - expected_defect)
    assert_zero("Krein/J flux preservation S.T*J*S=J", S.T * J * S - J)

    print("OK non-Hermitian S-matrix defect SymPy witness completed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
