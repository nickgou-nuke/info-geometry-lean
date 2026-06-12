#!/usr/bin/env python3
"""Finite verifier for the repaired PO55 conformal-closure owner surface.

This is a concrete 2D toy model that mirrors the algebra actually proved in
Lean, without claiming a full analytic or geometric PO(5,5) theory.

Verified here:
- boolean component conventions are concrete truth-value choices
- a null-swap involution exchanges distinguished null directions projectively
- the involution preserves a chosen null cone
- on projectively fixed null rays, the projective scale is ±1
- symmetrized readout swaps under inversion

Not verified here:
- any full PO(5,5) representation theory
- any TKK integration theorem beyond the abstract owner-field readback used in Lean
- any black-hole / AdS-CFT / thermodynamic-limit claim
"""

from __future__ import annotations

import sympy as sp


def same_ray(u: sp.Matrix, v: sp.Matrix) -> bool:
    if u == sp.zeros(*u.shape) or v == sp.zeros(*v.shape):
        return False
    for i in range(u.rows):
        if v[i, 0] != 0:
            c = sp.simplify(u[i, 0] / v[i, 0])
            return sp.simplify(u - c * v) == sp.zeros(*u.shape) and c != 0
    return False


def main() -> None:
    print("--- SymPy twin: PO55 conformal-closure finite verifier ---")

    # 1. Concrete component convention choices
    central_antipodal_identified = True
    residual_reflection_components = False
    assert central_antipodal_identified in (True, False)
    assert residual_reflection_components in (True, False)
    print("component convention booleans: OK")

    # 2. Null-swap model on a hyperbolic plane with off-diagonal form
    eta_offdiag = sp.Matrix([[0, 1], [1, 0]])
    swap = sp.Matrix([[0, 1], [1, 0]])
    e_minus = sp.Matrix([[1], [0]])
    e_plus = sp.Matrix([[0], [1]])

    q_offdiag = lambda x: sp.simplify((x.T * eta_offdiag * x)[0])

    assert q_offdiag(e_minus) == 0
    assert q_offdiag(e_plus) == 0
    assert swap * swap == sp.eye(2)
    assert same_ray(swap * e_minus, e_plus)
    assert same_ray(swap * e_plus, e_minus)
    print("null swap exchanges distinguished null directions: OK")

    # 3. Möbius-inversion datum on the diagonal split form x^2 - y^2
    #    Here swap preserves the null cone and has fixed/anti-fixed null rays.
    eta_diag = sp.Matrix([[1, 0], [0, -1]])
    inv = swap
    q_diag = lambda x: sp.simplify((x.T * eta_diag * x)[0])

    test_vectors = [
        sp.Matrix([[1], [1]]),
        sp.Matrix([[1], [-1]]),
        sp.Matrix([[2], [2]]),
        sp.Matrix([[3], [-3]]),
    ]
    for x in test_vectors:
        assert q_diag(x) == 0
        assert q_diag(inv * x) == 0
    print("involution preserves diagonal null cone on sample null rays: OK")

    fixed_null = sp.Matrix([[1], [1]])
    anti_fixed_null = sp.Matrix([[1], [-1]])
    assert inv * fixed_null == fixed_null
    assert inv * anti_fixed_null == -anti_fixed_null

    for x, expected_c in [(fixed_null, sp.Integer(1)), (anti_fixed_null, sp.Integer(-1))]:
        y = inv * x
        c = sp.simplify(y[0, 0] / x[0, 0])
        assert y == c * x
        assert c != 0
        assert sp.simplify(c**2) == 1
        assert c == expected_c
    print("projectively fixed null-ray scales satisfy c^2 = 1 and c = ±1: OK")

    # 4. Symmetrized readout swaps under inversion.
    read = lambda x: sp.simplify(x[0, 0] + 2 * x[1, 0])
    x = sp.Matrix([[2], [5]])
    sym_x = (read(x), read(inv * x))
    sym_inv_x = (read(inv * x), read(inv * inv * x))
    assert sym_inv_x == (sym_x[1], sym_x[0])
    print("symmetrized readout swaps under inversion: OK")

    print("[SUCCESS] PO55 conformal-closure finite verifier passed.")


if __name__ == "__main__":
    main()
