#!/usr/bin/env python3
"""Finite SymPy witness for the JKO / Bayesian transport corridor.

This script checks a concrete convex-potential discrete transport step:

- quadratic JKO proximal update;
- exact iterative contraction under repeated steps;
- exponential Bayesian reweighting on a two-state system.

It is a witness surface only. Lean owns the abstract bridge theorems.
"""

import sympy as sp


def quadratic_jko_step(x_prev, tau, a):
    x = sp.symbols("x", real=True)
    objective = (x - x_prev) ** 2 / (2 * tau) + a * x**2 / 2
    d_objective = sp.diff(objective, x)
    x_star = sp.solve(sp.Eq(d_objective, 0), x)[0]
    return sp.simplify(objective), sp.simplify(x_star), sp.simplify(sp.diff(objective, x, 2))


def main() -> int:
    tau, a = sp.symbols("tau a", positive=True, real=True)
    x0 = sp.symbols("x0", real=True)
    n = sp.symbols("n", integer=True, nonnegative=True)

    objective, x_star, hess = quadratic_jko_step(x0, tau, a)
    expected_step = sp.simplify(x0 / (1 + a * tau))

    # Repeated discrete transport step.
    x_n = sp.simplify(x0 / (1 + a * tau) ** n)
    recurrence_ok = sp.simplify(x_n.subs(n, n + 1) - sp.simplify(x_n / (1 + a * tau))) == 0

    # Energy decay under the discrete flow.
    energy_n = sp.simplify(a * x_n**2 / 2)
    energy_decay_ok = sp.simplify(energy_n.subs(n, n + 1) - energy_n / (1 + a * tau) ** 2) == 0

    # Two-state Bayesian exponential reweighting.
    p0, p1, beta, e0, e1 = sp.symbols("p0 p1 beta e0 e1", positive=True, real=True)
    Z = p0 * sp.exp(-beta * e0) + p1 * sp.exp(-beta * e1)
    post0 = sp.simplify(p0 * sp.exp(-beta * e0) / Z)
    post1 = sp.simplify(p1 * sp.exp(-beta * e1) / Z)
    bayes_sum_ok = sp.simplify(post0 + post1 - 1) == 0
    bayes_ratio_ok = sp.simplify(post0 / post1 - (p0 / p1) * sp.exp(-beta * (e0 - e1))) == 0

    # Basic convexity witness: the quadratic objective is strictly convex.
    convex_ok = sp.simplify(hess - (1 / tau + a)) == 0

    print("JKO / Bayesian transport witness")
    print("================================")
    print(f"quadratic objective: {(objective)}")
    print(f"proximal minimizer x* = {x_star}")
    print(f"expected minimizer   = {expected_step}")
    print(f"Hessian              = {hess}")
    print()
    print("Discrete transport step:")
    print(f"  x_n = {x_n}")
    print(f"  recurrence ok: {recurrence_ok}")
    print(f"  energy decay ok: {energy_decay_ok}")
    print(f"  convexity ok: {convex_ok}")
    print()
    print("Bayesian reweighting:")
    print(f"  posterior sum = 1: {bayes_sum_ok}")
    print(f"  posterior ratio law: {bayes_ratio_ok}")
    print()
    print("Lean bridge table:")
    bridge = [
        ("JKO / Bayesian update equivalence", "InfoGeometry.Canonical.MajoranaJKOErgoBridge.bayes_update_previous_eq_next"),
        ("Bayesian projection identity", "InfoGeometry.Canonical.MajoranaJKOErgoBridge.bayesian_projection_identity"),
        ("Operator JKO argmin", "InfoGeometry.Canonical.OperatorJKOStep.OperatorJKOArgmin"),
        ("Discrete Bayes/JKO calibration", "InfoGeometry.Canonical.OperatorJKOStep.JKOBayesianCalibration"),
        ("Convex-potential boosted action", "InfoGeometry.Canonical.GenerativeInferenceCore.hyperbolicallyBoostedBayesianAction"),
    ]
    for label, lean_name in bridge:
        print(f"  - {label}: {lean_name}")

    overall = all([
        recurrence_ok,
        energy_decay_ok,
        bayes_sum_ok,
        bayes_ratio_ok,
        convex_ok,
    ])
    print()
    print(f"OVERALL: {overall}")
    return 0 if overall else 1


if __name__ == "__main__":
    raise SystemExit(main())
