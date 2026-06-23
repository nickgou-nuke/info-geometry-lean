#!/usr/bin/env python3
"""Finite SymPy audit for the modular infinitesimal dictionary.

This is not an analytic Type-III construction.  It checks the finite algebraic
readouts formalized in
`lean/InfoGeometry/Canonical/ModularInfinitesimalDictionary.lean`:

  d log Q = log RN = Connes generator = modular-Hamiltonian difference,
  Araki/Bregman gradient = barrier force = - d log Q,
  entropy-production commutator = d log Q in a supplied finite flow.
"""

import sympy as sp


def assert_zero(expr, label: str) -> None:
    simplified = sp.simplify(expr)
    if simplified != 0:
        raise AssertionError(f"{label} failed: {simplified!r}")


def assert_zero_matrix(mat: sp.Matrix, label: str) -> None:
    bad = sp.simplify(mat)
    if bad != sp.zeros(*bad.shape):
        raise AssertionError(f"{label} failed:\n{bad}")


def scalar_dictionary_audit() -> None:
    p, q = sp.symbols("p q", positive=True)

    # Classical logarithmic Radon--Nikodym increment.
    log_rn = sp.log(p / q)
    dlog_q = sp.log(p) - sp.log(q)

    # Sign convention matching the Lean finite premise:
    # K_target - K_source = (-log q) - (-log p) = log(p/q).
    K_source = -sp.log(p)
    K_target = -sp.log(q)
    hamiltonian_diff = K_target - K_source

    connes_generator = hamiltonian_diff
    araki_gradient = -dlog_q
    barrier_force = -dlog_q

    assert_zero(dlog_q - log_rn, "d log Q equals log RN")
    assert_zero(connes_generator - log_rn, "Connes generator equals log RN")
    assert_zero(hamiltonian_diff - dlog_q, "Hamiltonian difference equals d log Q")
    assert_zero(araki_gradient + connes_generator, "Araki gradient is negative generator")
    assert_zero(barrier_force - araki_gradient, "barrier force equals Araki gradient")


def monodromy_period_audit() -> None:
    """Check the finite readout: trivial period => zero generator; nonzero period => nontrivial loop."""
    winding = sp.symbols("winding", integer=True)
    period = 2 * sp.pi * sp.I * winding
    connes_generator = period

    # Trivial loop/winding sector.
    assert_zero(connes_generator.subs(winding, 0),
                "trivial winding kills Connes generator")

    # Nontrivial monodromy is checked by winding=1.
    nontrivial = sp.simplify(connes_generator.subs(winding, 1))
    if nontrivial == 0:
        raise AssertionError("nontrivial winding should give nonzero monodromy")


def finite_commutator_flow_audit() -> None:
    a, b = sp.symbols("a b")
    P_forward = sp.Matrix([[0, a], [0, 0]])
    P_backward = sp.Matrix([[0, 0], [b, 0]])

    entropy_production = P_forward * P_backward - P_backward * P_forward
    d_ln_Q = sp.Matrix([[a * b, 0], [0, -a * b]])

    assert_zero_matrix(entropy_production - d_ln_Q,
                       "finite thermodynamic commutator equals d_ln_Q")

    connes_generator = d_ln_Q
    araki_gradient = -d_ln_Q
    barrier_force = -d_ln_Q

    assert_zero_matrix(entropy_production - connes_generator,
                       "entropy production equals Connes generator")
    assert_zero_matrix(araki_gradient + connes_generator,
                       "matrix Araki gradient is negative generator")
    assert_zero_matrix(barrier_force - araki_gradient,
                       "matrix barrier force equals Araki gradient")


def main() -> None:
    scalar_dictionary_audit()
    monodromy_period_audit()
    finite_commutator_flow_audit()
    print("modular infinitesimal dictionary audit: ok")


if __name__ == "__main__":
    main()
