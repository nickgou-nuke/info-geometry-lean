#!/usr/bin/env python3
"""
Finite Clifford-braiding central-core validator.

Certified exact content:
  * concrete 2x2 integer matrices J,E with J^2=-I, E^2=I, EJ+JE=0;
  * conjugation by J preserves the central core {+I,-I};
  * the split pseudoscalar P=EJ has P^2=I;
  * optional clifford/galgebra lanes are probed, not required.

Not claimed: a general Clifford-module braiding theorem, anyon statistics,
Lorentz/Pin/Spin representation theory, parafermion CFT, super-Kähler geometry, or categorical
hexagon coherence.
"""

from __future__ import annotations

import json
from typing import Any

import sympy as sp


def assert_zero_matrix(M: sp.Matrix, label: str) -> None:
    if M != sp.zeros(*M.shape):
        raise AssertionError(f"{label} not zero: {M}")


def verify_sympy() -> dict[str, bool]:
    I2 = sp.eye(2)
    J = sp.Matrix([[0, 1], [-1, 0]])
    E = sp.Matrix([[1, 0], [0, -1]])
    P = E * J
    Jinverse = -J

    assert_zero_matrix(J * J + I2, "J^2 + I")
    assert_zero_matrix(E * E - I2, "E^2 - I")
    assert_zero_matrix(E * J + J * E, "EJ + JE")
    assert_zero_matrix(P * P - I2, "P^2 - I")
    assert_zero_matrix(J * Jinverse - I2, "J inverse right")
    assert_zero_matrix(Jinverse * J - I2, "J inverse left")
    assert_zero_matrix(J * I2 * Jinverse - I2, "J I J^-1 - I")
    assert_zero_matrix(J * (-I2) * Jinverse + I2, "J(-I)J^-1 + I")
    assert_zero_matrix(J * (-I2) - (-I2) * J, "central inversion commutator")

    return {
        "J_square_minus_I": True,
        "E_square_I": True,
        "E_anticommutes_J": True,
        "pseudoscalar_square_I": True,
        "central_core_preserved_by_J_conjugation": True,
    }


def verify_optional_clifford() -> dict[str, Any]:
    try:
        import clifford  # type: ignore
    except Exception as exc:
        return {"available": False, "reason": f"{exc.__class__.__name__}: {exc}"}

    layout, blades = clifford.Cl(1, 1, firstIdx=1)
    e1 = blades["e1"]
    e2 = blades["e2"]
    ps = e1 * e2
    assert (e1 * e1)[()] == 1
    assert (e2 * e2)[()] == -1
    assert e1 * e2 + e2 * e1 == 0
    assert (ps * ps)[()] == 1
    return {"available": True, "cl11_signs_ok": True, "dims": layout.dims}


def verify_optional_galgebra() -> dict[str, Any]:
    try:
        from galgebra.ga import Ga  # type: ignore
    except Exception as exc:
        return {"available": False, "reason": f"{exc.__class__.__name__}: {exc}"}

    ga = Ga("e f", g=[1, -1])
    e, f = ga.mv()
    ps = e * f
    assert str(e * e) == "1"
    assert str(f * f) == "-1"
    assert str(e * f + f * e) == "0"
    assert str(ps * ps) == "1"
    return {"available": True, "cl11_signs_ok": True}


def verify_cyclotomic_center_root() -> dict[str, bool]:
    z = sp.symbols("z")
    G = sp.groebner([z**2 + 1], z, order="lex", domain=sp.QQ)
    rem = G.reduce(sp.Poly(z**2 + 1, z, domain=sp.QQ))[1]
    if rem.as_expr() != 0:
        raise AssertionError("z^2=-1 quotient reduction failed")
    return {"z_square_is_central_inversion": True}


if __name__ == "__main__":
    result = {
        "sympy": verify_sympy(),
        "cyclotomic_root": verify_cyclotomic_center_root(),
        "clifford_optional": verify_optional_clifford(),
        "galgebra_optional": verify_optional_galgebra(),
    }
    print("CLIFFORD_BRAIDING_CENTER_FINITE_PACKET_OK")
    print(json.dumps(result, sort_keys=True))
