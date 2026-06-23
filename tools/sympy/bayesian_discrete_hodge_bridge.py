#!/usr/bin/env python3
"""Finite Bayesian/MaxCal/discrete-Hodge bridge witness.

This script is a finite symbolic/numeric audit for the Lean bridge:

* Bayesian update as an orthogonal projection onto a supplied Hodge constraint;
* exact, coexact, and harmonic current sectors on the K3 incidence model;
* harmonic code-space protection against local exact/coexact sectors;
* explicit MaxCal entropy-current readout calibration to a coexact current.

No analytic convergence, QMS construction, or continuum Hodge theorem is
asserted here.
"""

from __future__ import annotations

import sympy as sp


def assert_zero(name: str, mat: sp.Matrix) -> None:
    simplified = mat.applyfunc(sp.simplify)
    if simplified != sp.zeros(*simplified.shape):
        raise AssertionError(f"{name} failed:\n{simplified}")
    print(f"ok: {name}")


def incidence_k3() -> tuple[sp.Matrix, sp.Matrix]:
    d0 = sp.Matrix([
        [-1, 1, 0],
        [0, -1, 1],
        [-1, 0, 1],
    ])
    d1 = sp.Matrix([[1, 1, -1]])
    return d0, d1


def projection_onto(vector: sp.Matrix) -> sp.Matrix:
    denom = (vector.T * vector)[0]
    return vector * vector.T / denom


def verify_bayesian_projection_to_harmonic_constraint() -> None:
    d0, _ = incidence_k3()
    harmonic = sp.Matrix([1, 1, -1])
    prior = sp.Matrix([2, -1, 4])
    projector = projection_onto(harmonic)
    posterior = sp.simplify(projector * prior)

    l1_boundary = d0 * d0.T
    assert_zero("posterior lies in boundary harmonic constraint", l1_boundary * posterior)
    assert_zero("posterior is coclosed", d0.T * posterior)
    assert_zero("Markov projection is idempotent", projector * projector - projector)
    assert_zero("posterior is stationary for projection", projector * posterior - posterior)

    residual = prior - posterior
    if sp.simplify((harmonic.T * residual)[0]) != 0:
        raise AssertionError("Bayesian projection residual is not orthogonal to harmonic constraint")
    print("ok: Bayesian projection residual is orthogonal to harmonic code space")


def verify_sector_readouts() -> None:
    d0, d1 = incidence_k3()
    phi = sp.Matrix([3, -2, 1])
    exact = d0 * phi
    psi = sp.Matrix([5])
    coexact = d1.T * psi
    boundary_harmonic = sp.Matrix([1, 1, -1])

    assert_zero("exact current is closed", d1 * exact)
    assert_zero("coexact current is coclosed", d0.T * coexact)
    if sp.simplify((exact.T * coexact)[0]) != 0:
        raise AssertionError("exact and coexact sectors are not orthogonal")
    print("ok: filled exact and coexact sectors are orthogonal")

    # The boundary K3 graph has no faces, so the boundary cycle is the harmonic
    # code mode.  After adding the 2-simplex, this same vector becomes the
    # coexact face sector and is no longer harmonic.
    l1_boundary = d0 * d0.T
    assert_zero("boundary harmonic current is in ker L1", l1_boundary * boundary_harmonic)
    assert_zero("boundary harmonic current is coclosed", d0.T * boundary_harmonic)
    if sp.simplify((boundary_harmonic.T * exact)[0]) != 0:
        raise AssertionError("boundary harmonic current not orthogonal to exact sector")
    print("ok: boundary harmonic current is protected from exact sector")


def verify_maxcal_coexact_readout_calibration() -> None:
    _, d1 = incidence_k3()
    entropy = sp.symbols("S_prod")
    coexact_generator = d1.T
    current = coexact_generator * sp.Matrix([entropy / 3])

    # Read out the oriented loop average.  With current=(S/3,S/3,-S/3),
    # the K3 face row [1,1,-1] returns S.
    current_readout = (d1 * current)[0]
    d_ln_q = sp.symbols("d_ln_Q")
    calibrated = current_readout.subs(entropy, d_ln_q)
    if sp.simplify(calibrated - d_ln_q) != 0:
        raise AssertionError("coexact MaxCal readout does not calibrate to d_ln_Q")
    print("ok: coexact MaxCal current readout calibrates to d_ln_Q")


def main() -> None:
    print("=== Bayesian / Discrete Hodge Bridge Witness ===")
    verify_bayesian_projection_to_harmonic_constraint()
    verify_sector_readouts()
    verify_maxcal_coexact_readout_calibration()
    print("=== SUCCESS ===")


if __name__ == "__main__":
    main()
