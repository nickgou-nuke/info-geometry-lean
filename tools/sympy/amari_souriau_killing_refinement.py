#!/usr/bin/env python3
"""
SymPy witness for the Hessian/Killing refinement of the Amari--Souriau bridge.

This script checks a conservative constant-metric quadratic model where:
- the Hessian/Fisher metric is constant,
- the natural-gradient flow vanishes at the target,
- the corresponding constant translation field has zero Lie derivative on the metric,
- the de Rham/log-partition force is exact in equilibrium.
"""

from __future__ import annotations

import sympy as sp


def main() -> None:
    print("=== SYMPY: AMARI-SOURIAU HESSIAN/KILLING REFINEMENT ===")

    θ1, θ2, β1, β2 = sp.symbols("theta1 theta2 beta1 beta2", real=True)
    θ = sp.Matrix([θ1, θ2])
    θ_star = sp.Matrix([β1, β2])

    G = sp.Matrix([[2, 1], [1, 3]])
    print("\n1. Constant Hessian/Fisher metric G:")
    sp.pprint(G)

    Ψ = sp.Rational(1, 2) * (θ.T * G * θ)[0]
    gradΨ = sp.Matrix([sp.diff(Ψ, θ1), sp.diff(Ψ, θ2)])
    η_star = G * θ_star

    print("\n2. Potential Ψ and gradient η = ∇Ψ:")
    sp.pprint(Ψ)
    sp.pprint(gradΨ)

    theta_flow = -(θ - θ_star)
    eta_flow = -(gradΨ - η_star)

    print("\n3. Primal natural-gradient flow θdot:")
    sp.pprint(theta_flow)
    print("Dual relaxation ηdot:")
    sp.pprint(eta_flow)

    theta_flow_target = sp.simplify(theta_flow.subs({θ1: β1, θ2: β2}))
    eta_flow_target = sp.simplify(eta_flow.subs({θ1: β1, θ2: β2}))
    print("\n4. Target fixed-point evaluation:")
    print("theta_flow(θ*) =")
    sp.pprint(theta_flow_target)
    print("eta_flow(θ*) =")
    sp.pprint(eta_flow_target)
    assert theta_flow_target == sp.zeros(2, 1)
    assert eta_flow_target == sp.zeros(2, 1)

    # Lie derivative of a constant metric along a constant-translation field is zero.
    x1, x2, c1, c2 = sp.symbols("x1 x2 c1 c2", real=True)
    X = sp.Matrix([c1, c2])
    metric_entries = {(1, 1): sp.Integer(2), (1, 2): sp.Integer(1), (2, 1): sp.Integer(1), (2, 2): sp.Integer(3)}
    lie_entries = {}
    coords = [x1, x2]
    for i in range(2):
        for j in range(2):
            gij = metric_entries[(i + 1, j + 1)]
            term = sp.Integer(0)
            for k in range(2):
                term += X[k] * sp.diff(gij, coords[k])
            term += sum(sp.diff(X[k], coords[i]) * metric_entries[(k + 1, j + 1)] for k in range(2))
            term += sum(sp.diff(X[k], coords[j]) * metric_entries[(i + 1, k + 1)] for k in range(2))
            lie_entries[(i, j)] = sp.simplify(term)

    print("\n5. Lie derivative components L_X g for constant Hessian metric:")
    lie_matrix = sp.Matrix([[lie_entries[(0, 0)], lie_entries[(0, 1)]], [lie_entries[(1, 0)], lie_entries[(1, 1)]]])
    sp.pprint(lie_matrix)
    assert lie_matrix == sp.zeros(2, 2)

    Q = sp.exp(Ψ)
    dlogQ = sp.Matrix([sp.diff(sp.log(Q), θ1), sp.diff(sp.log(Q), θ2)])
    print("\n6. Exact de Rham/log-partition force d(log Q):")
    sp.pprint(dlogQ)
    assert sp.simplify(dlogQ - gradΨ) == sp.zeros(2, 1)

    print("\nCONCLUSION:")
    print("  - The Hessian metric is constant in the quadratic model.")
    print("  - The natural-gradient flow has a genuine fixed point at θ*.")
    print("  - The dual flow also vanishes at θ*.")
    print("  - Any constant-translation field has zero Lie derivative on g.")
    print("  - d(log Q) remains exact and agrees with ∇Ψ in equilibrium.")


if __name__ == "__main__":
    main()
