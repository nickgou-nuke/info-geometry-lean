#!/usr/bin/env python3
"""
Exact finite parafermion/central-root witness.

Checks the Z_3 clock/shift relation X Z = omega Z X over the cyclotomic
quotient Phi_3(omega)=0 and the concrete real 2x2 complex-structure matrix
J^2=-I.  Optional Galgebra availability is reported but not required.
"""

from __future__ import annotations

import json
from typing import Any

import sympy as sp

w = sp.symbols("w")
G = sp.groebner([w**2 + w + 1], w, order="lex", domain=sp.QQ)


def red(expr):
    expr = sp.expand(expr)
    rem = G.reduce(sp.Poly(expr, w, domain=sp.QQ))[1]
    return sp.expand(rem.as_expr())


def red_matrix(M):
    return M.applyfunc(red)


def assert_zero_matrix(name, M):
    R = red_matrix(M)
    if any(R[i, j] != 0 for i in range(R.rows) for j in range(R.cols)):
        raise AssertionError(f"{name} failed:\n{R}")
    print(f"PASS: {name}")


def optional_galgebra() -> dict[str, Any]:
    try:
        from galgebra.ga import Ga  # type: ignore
    except Exception as exc:
        return {"available": False, "reason": f"{exc.__class__.__name__}: {exc}"}
    ga = Ga("e1 e2 e3", g=[1, 1, 1])
    e1, e2, e3 = ga.mv()
    J = e1 ^ e2 ^ e3
    return {"available": True, "pseudoscalar_square_repr": str(J * J)}


def main() -> None:
    I2 = sp.eye(2)
    J = sp.Matrix([[0, 1], [-1, 0]])
    assert J * J == -I2
    print("PASS: real central root J^2=-I")

    X = sp.Matrix([[0, 1, 0], [0, 0, 1], [1, 0, 0]])
    Z = sp.diag(1, w, w**2)
    I3 = sp.eye(3)

    assert_zero_matrix("omega^3=1", sp.Matrix([[w**3 - 1]]))
    assert_zero_matrix("X^3=I", X**3 - I3)
    assert_zero_matrix("Z^3=I", Z**3 - I3)
    assert_zero_matrix("XZ = omega ZX", X * Z - w * Z * X)

    result = {
        "z3_clock_shift": True,
        "central_root_J_square_minus_I": True,
        "galgebra_optional": optional_galgebra(),
    }
    print("PARAFERMION_CLIFFORD_ROOTS_FINITE_OK")
    print(json.dumps(result, sort_keys=True))


if __name__ == "__main__":
    main()
