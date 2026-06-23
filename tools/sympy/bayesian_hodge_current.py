#!/usr/bin/env python3
"""Finite symbolic audit for Bayesian Hodge edge currents.

This mirrors `InfoGeometry.Canonical.BayesianHodgeCurrent`.

Checked finite claims:
* Bayes odds update and two-state stationary detailed balance;
* exact edge currents are closed (`d1*d0 = 0`);
* coexact loop currents are coclosed (`d0.T*d1.T = 0`);
* exact and coexact sectors are orthogonal;
* a harmonic hollow-triangle current is in the Hodge kernel and is orthogonal
  to exact local currents;
* MaxCal log-ratio changes sign under path reversal.
"""

from __future__ import annotations

import sympy as sp


def require_zero(name: str, expr) -> None:
    simplified = sp.simplify(expr)
    if getattr(simplified, "shape", None) is not None:
        simplified = simplified.applyfunc(sp.simplify)
        if simplified != sp.zeros(*simplified.shape):
            raise AssertionError(f"{name} failed:\n{simplified}")
    elif simplified != 0:
        raise AssertionError(f"{name} failed: {simplified}")
    print(f"[ok] {name}")


def bayesian_two_state_checks() -> None:
    a, b = sp.symbols("a b", positive=True)
    p0, p1, l0, l1 = sp.symbols("p0 p1 l0 l1", positive=True)

    transition = sp.Matrix([[1 - a, a], [b, 1 - b]])
    stationary = sp.Matrix([[b / (a + b), a / (a + b)]])

    require_zero("two-state stationary Markov law", stationary * transition - stationary)
    require_zero("two-state detailed balance", stationary[0, 0] * a - stationary[0, 1] * b)
    require_zero("two-state normalization", stationary[0, 0] + stationary[0, 1] - 1)

    prior0 = p0 / (p0 + p1)
    prior1 = p1 / (p0 + p1)
    evidence = prior0 * l0 + prior1 * l1
    posterior0 = prior0 * l0 / evidence
    posterior1 = prior1 * l1 / evidence

    require_zero("Bayes posterior normalization", posterior0 + posterior1 - 1)
    require_zero("Bayes odds update", posterior0 / posterior1 - (p0 / p1) * (l0 / l1))


def hodge_current_checks() -> None:
    # Filled oriented triangle: vertices 0,1,2; edges 01,12,02; face 012.
    d0 = sp.Matrix(
        [
            [-1, 1, 0],
            [0, -1, 1],
            [-1, 0, 1],
        ]
    )
    d1 = sp.Matrix([[-1, -1, 1]])

    require_zero("cochain condition d1*d0", d1 * d0)
    require_zero("adjoint cochain condition d0.T*d1.T", d0.T * d1.T)

    phi0, phi1, phi2, psi = sp.symbols("phi0 phi1 phi2 psi")
    exact_current = d0 * sp.Matrix([phi0, phi1, phi2])
    loop_current = d1.T * sp.Matrix([psi])

    require_zero("exact current is closed", d1 * exact_current)
    require_zero("coexact loop current is coclosed", d0.T * loop_current)
    require_zero("exact and coexact currents orthogonal", exact_current.dot(loop_current))

    # Hollow triangle: no face term, so the one-cycle is harmonic.
    hollow_L1 = d0 * d0.T
    harmonic = sp.Matrix([1, 1, -1])
    require_zero("hollow harmonic current is coclosed", d0.T * harmonic)
    require_zero("hollow harmonic current is in Hodge kernel", hollow_L1 * harmonic)
    require_zero("hollow harmonic current orthogonal to exact current", harmonic.dot(exact_current))

    lam, cf, cb = sp.symbols("lambda c_forward c_backward")
    maxcal_log_ratio = -lam * (cf - cb)
    maxcal_reverse = -lam * (cb - cf)
    require_zero("MaxCal log-ratio reversal", maxcal_reverse + maxcal_log_ratio)
    require_zero("MaxCal detailed-balance log-ratio", -lam * (cf - cf))

    print("filled exact current =", exact_current.T)
    print("filled loop current =", loop_current.T)
    print("hollow harmonic current =", harmonic.T)


def main() -> None:
    bayesian_two_state_checks()
    hodge_current_checks()


if __name__ == "__main__":
    main()
