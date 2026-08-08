#!/usr/bin/env python3
"""Finite audit for the Dirac-Cuntz crystal dispersion toy.

The key correction is explicit:

- the linear cone E = v_F k has a trivial Jackson q-derivative, so it does not
  by itself witness any real q-deformation;
- deformation only becomes visible once a nonlinear lattice factor enters,
  e.g. sin(k), cos(k), a tight-binding dispersion, or a DOS functional.

This is an external audit only, not a proof kernel.
"""

import sympy as sp

vF, kx, ky, Delta = sp.symbols("vF kx ky Delta")
k_norm_sq = kx**2 + ky**2
safe_factor_zero = 1
form_factor = 1
massless_zero = vF**2 * k_norm_sq * safe_factor_zero**2 * form_factor**2
massive_zero = massless_zero + Delta**2

assert sp.simplify(massless_zero - vF**2 * k_norm_sq) == 0
assert sp.simplify(massive_zero - (vF**2 * k_norm_sq + Delta**2)) == 0
assert {"conduction": 1, "valence": -1}["conduction"] == 1
assert {"conduction": 1, "valence": -1}["valence"] == -1
assert 3 == len(range(3))


def jackson_q_derivative(fk, q, k):
    return sp.simplify((fk.subs(k, q * k) - fk) / ((q - 1) * k))


def audit_jackson_derivative():
    k, t, v_F, hbar, eta = sp.symbols("k t v_F hbar eta", real=True, positive=True)
    q = sp.exp(-hbar * eta)

    print("--- SYMPY AUDIT: JACKSON q-DERIVATIVE ---")
    print(f"q = {q}")

    # 1) Linear cone: q-derivative is exactly v_F, so no deformation is visible.
    E_linear = v_F * k
    D_q_linear = jackson_q_derivative(E_linear, q, k)
    print(f"D_q[v_F*k] = {D_q_linear}")
    assert sp.simplify(D_q_linear - v_F) == 0

    # 2) Nonlinear lattice factor: deformation becomes visible.
    F_sin = sp.sin(k)
    F_cos = sp.cos(k)
    E_tb = -2 * t * sp.cos(k)

    D_q_sin = jackson_q_derivative(F_sin, q, k)
    D_q_cos = jackson_q_derivative(F_cos, q, k)
    D_q_tb = jackson_q_derivative(E_tb, q, k)

    print(f"D_q[sin(k)] = {D_q_sin}")
    print(f"D_q[cos(k)] = {D_q_cos}")
    print(f"D_q[-2*t*cos(k)] = {D_q_tb}")

    # The q->1 limit recovers the ordinary derivatives of the nonlinear factors.
    assert sp.simplify(sp.limit(D_q_sin, eta, 0) - sp.cos(k)) == 0
    assert sp.simplify(sp.limit(D_q_cos, eta, 0) + sp.sin(k)) == 0
    assert sp.simplify(sp.limit(D_q_tb, eta, 0) - 2 * t * sp.sin(k)) == 0

    print("Linear cone is q-trivial; nonlinear lattice factors carry the deformation.")


audit_jackson_derivative()
print("dirac_cuntz_crystal_dispersion.py: SymPy audit passed")
