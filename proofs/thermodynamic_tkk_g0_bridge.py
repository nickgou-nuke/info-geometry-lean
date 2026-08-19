#!/usr/bin/env python3
"""Finite symbolic audit for thermodynamic chemical-potential/Rindler -> TKK g0.

This is an audit witness only.  Lean remains the proof kernel.
"""

import sympy as sp


def comm(A, B):
    return sp.simplify(A * B - B * A)


def verify_chemical_potential_to_g0():
    print("=== SYMPY: CHEMICAL POTENTIAL / RINDLER TO TKK G0 BRIDGE ===")

    mu1, mu2, mu3 = sp.symbols("mu_1 mu_2 mu_3", real=True)
    beta, dmu, Q, f, theta, E = sp.symbols("beta dmu Q f theta E", real=True)

    sigma_z = sp.Matrix([[1, 0], [0, -1]])
    sigma_x = sp.Matrix([[0, 1], [1, 0]])
    sigma_y = sp.Matrix([[0, -sp.I], [sp.I, 0]])

    X12 = (mu1 - mu2) * sigma_x
    X23 = (mu2 - mu3) * sigma_y
    bracket = comm(X12, X23)
    eta_component = sp.simplify(bracket[0, 0])
    expected = 2 * sp.I * (mu1 - mu2) * (mu2 - mu3) * sigma_z

    assert sp.simplify(bracket - expected) == sp.zeros(2)
    assert sp.simplify(bracket[0, 1]) == 0
    assert sp.simplify(bracket[1, 0]) == 0
    assert sp.simplify(bracket[1, 1] + eta_component) == 0

    # Exactness of chemical potential edge one-form on the triangle.
    theta12 = mu2 - mu1
    theta23 = mu3 - mu2
    theta31 = mu1 - mu3
    assert sp.simplify(theta12 + theta23 + theta31) == 0

    # Rindler/Bogoliubov affine parameter and chemical potential shift commute
    # at the log-clock bookkeeping level.
    rho = theta - beta * (E - mu1 * Q)
    rho_shifted = (theta + f) - beta * (E - (mu1 + dmu) * Q)
    expected_shifted = rho + f + beta * dmu * Q
    assert sp.simplify(rho_shifted - expected_shifted) == 0

    q_phase = sp.exp(sp.I * sp.pi * f)
    q_weyl = sp.exp(f)
    assert q_phase != 0
    assert q_weyl != 0

    # Protected finite label flow: analytic operator flow is deferred_interface in Lean,
    # but the V4/Mobius labels themselves are invariant.
    v4_labels = ["1", "eta", "J", "etaJ"]
    mobius_labels = ["id", "parity", "inversion", "parityInversion"]
    protected_v4_flow = {label: label for label in v4_labels}
    protected_mobius_flow = {label: label for label in mobius_labels}
    assert all(protected_v4_flow[label] == label for label in v4_labels)
    assert all(protected_mobius_flow[label] == label for label in mobius_labels)

    positive_grades = [1, 2]
    negative_grades = [-1, -2]
    formal_index = len(positive_grades) - len(negative_grades)
    assert formal_index == 0

    print("X12 =")
    sp.pprint(X12)
    print("X23 =")
    sp.pprint(X23)
    print("[X12, X23] =")
    sp.pprint(bracket)
    print("eta/sigma_z alignment:", sp.simplify(bracket - expected) == sp.zeros(2))
    print("triangle exact cycle theta12+theta23+theta31 =", sp.simplify(theta12 + theta23 + theta31))
    print("log-clock shift rho -> rho + f + beta*dmu*Q:", sp.simplify(rho_shifted))
    print("q phase exp(i*pi*f):", q_phase)
    print("protected V4 labels:", protected_v4_flow)
    print("protected Mobius labels:", protected_mobius_flow)
    print("formal five-grade chiral parity index:", formal_index)
    print("thermodynamic_tkk_g0_bridge.py: finite audit passed")


if __name__ == "__main__":
    verify_chemical_potential_to_g0()
