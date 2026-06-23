#!/usr/bin/env python3
"""
SymPy finite check for the Amari--Souriau thermodynamic gauge bridge.

This script checks a conservative finite-dimensional model of the dictionary:

1. Ψ = log Q for a positive partition function Q = exp(Ψ)
2. the Hessian of Ψ gives a constant Fisher/Hessian metric in a quadratic model
3. the Bregman divergence has the expected explicit form and vanishes on the diagonal
4. the natural-gradient flow induced by the quadratic Bregman divergence becomes
   linear relaxation in dual coordinates
5. d(log Q) = dΨ in the explicit model

It is a computational companion to the Lean owner
`InfoGeometry.Canonical.AmariSouriauThermodynamicGauge`.
"""

from __future__ import annotations

import sympy as sp


def main() -> None:
    print("=== SYMPY: AMARI-SOURIAU THERMODYNAMIC GAUGE FINITE CHECK ===")

    θ1, θ2, θ1p, θ2p = sp.symbols("theta1 theta2 theta1p theta2p", real=True)
    β1, β2 = sp.symbols("beta1 beta2", real=True)
    θ = sp.Matrix([θ1, θ2])
    θp = sp.Matrix([θ1p, θ2p])
    θ_star = sp.Matrix([β1, β2])

    G = sp.Matrix([[2, 1], [1, 3]])
    assert G.det() != 0
    print("\n1. Positive definite quadratic metric G:")
    sp.pprint(G)
    print("det(G) =", sp.factor(G.det()))

    Ψ = sp.Rational(1, 2) * (θ.T * G * θ)[0]
    Q = sp.exp(Ψ)
    print("\n2. Log-partition potential Ψ(θ) = 1/2 θᵀGθ:")
    sp.pprint(Ψ)
    print("Q(θ) = exp(Ψ(θ))")
    sp.pprint(Q)

    logQ = sp.simplify(sp.log(Q))
    print("log(Q) simplifies to:")
    sp.pprint(logQ)
    assert sp.simplify(logQ - Ψ) == 0

    gradΨ = sp.Matrix([sp.diff(Ψ, θ1), sp.diff(Ψ, θ2)])
    η = gradΨ
    print("\n3. Dual/expectation coordinates η = ∇Ψ:")
    sp.pprint(η)

    HessΨ = sp.hessian(Ψ, (θ1, θ2))
    print("\n4. Hessian/Fisher metric ∇²Ψ:")
    sp.pprint(HessΨ)
    assert sp.simplify(HessΨ - G) == sp.zeros(2, 2)

    Ψp = sp.Rational(1, 2) * (θp.T * G * θp)[0]
    grad_at_θ = gradΨ
    diff = θp - θ
    bregman = sp.simplify(Ψp - Ψ - (grad_at_θ.T * diff)[0])
    print("\n5. Bregman divergence D_Ψ(θ' || θ):")
    sp.pprint(bregman)

    expected_bregman = sp.simplify(sp.Rational(1, 2) * ((θp - θ).T * G * (θp - θ))[0])
    print("Expected quadratic form:")
    sp.pprint(expected_bregman)
    assert sp.simplify(bregman - expected_bregman) == 0

    bregman_self = sp.simplify(bregman.subs({θ1p: θ1, θ2p: θ2}))
    print("Diagonal specialization D_Ψ(θ || θ) =", bregman_self)
    assert bregman_self == 0

    Ginv = sp.simplify(G.inv())
    η_star = G * θ_star
    print("\n6. Inverse metric G⁻¹:")
    sp.pprint(Ginv)
    print("Target dual coordinate η*:")
    sp.pprint(η_star)

    # For the quadratic model, grad_θ D_Ψ(θ || θ*) = G(θ - θ*) = η - η*
    D_theta_to_star = sp.simplify(
        Ψ - sp.Rational(1, 2) * (θ_star.T * G * θ_star)[0] - ((η_star).T * (θ - θ_star))[0]
    )
    gradD = sp.Matrix([sp.diff(D_theta_to_star, θ1), sp.diff(D_theta_to_star, θ2)])
    print("\n7. Gradient of D_Ψ(θ || θ*):")
    sp.pprint(gradD)
    assert sp.simplify(gradD - (η - η_star)) == sp.zeros(2, 1)

    θdot = -Ginv * gradD
    print("Natural-gradient flow θdot = -G⁻¹ ∇D:")
    sp.pprint(θdot)
    assert sp.simplify(θdot + (θ - θ_star)) == sp.zeros(2, 1)

    ηdot = sp.simplify(G * θdot)
    print("Dual relaxation ηdot:")
    sp.pprint(ηdot)
    assert sp.simplify(ηdot + (η - η_star)) == sp.zeros(2, 1)

    dlogQ = sp.Matrix([sp.diff(logQ, θ1), sp.diff(logQ, θ2)])
    print("\n8. Differential of log(Q):")
    sp.pprint(dlogQ)
    print("Gradient of Ψ:")
    sp.pprint(gradΨ)
    assert sp.simplify(dlogQ - gradΨ) == sp.zeros(2, 1)

    exterior_dlogQ = sp.simplify(sp.diff(dlogQ[1], θ1) - sp.diff(dlogQ[0], θ2))
    print("Exterior derivative d(d log Q) in this 2D model =", exterior_dlogQ)
    assert exterior_dlogQ == 0

    # Constant Fisher/Hessian metric and constant vector field give zero Lie derivative.
    X1, X2 = sp.symbols("X1 X2", real=True)
    X = sp.Matrix([X1, X2])
    lie_metric = sp.zeros(2, 2)
    coords = [θ1, θ2]
    for i in range(2):
        for j in range(2):
            entry = sum(X[k] * sp.diff(G[i, j], coords[k]) for k in range(2))
            entry += sum(G[k, j] * sp.diff(X[k], coords[i]) for k in range(2))
            entry += sum(G[i, k] * sp.diff(X[k], coords[j]) for k in range(2))
            lie_metric[i, j] = sp.simplify(entry)
    print("Lie_X g for constant X in this model:")
    sp.pprint(lie_metric)
    assert lie_metric == sp.zeros(2, 2)

    print("\nCONCLUSION:")
    print("  - Ψ = log Q holds in the explicit positive model.")
    print("  - The Hessian metric is exactly the quadratic Fisher/Hessian tensor G.")
    print("  - The Bregman divergence is the expected quadratic energy gap.")
    print("  - The natural-gradient flow linearizes to ηdot = -(η - η*).")
    print("  - d(log Q) = dΨ, and d(d log Q) = 0 in this finite model.")
    print("  - Constant-field Lie derivative of the constant Fisher metric vanishes.")


if __name__ == "__main__":
    main()
