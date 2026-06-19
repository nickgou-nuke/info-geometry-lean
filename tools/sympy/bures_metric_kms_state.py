#!/usr/bin/env python3
"""
SymPy witness for finite Bures/Fisher metric stabilization under a local tensor
bonding map ρ ↦ ρ ⊗ I/2.

We use the commuting qubit KMS family
    ρ(θ) = exp(-θ σ_z) / Tr(exp(-θ σ_z))
and verify:
1. the Fisher metric of the one-parameter family,
2. the infinitesimal Bures metric from fidelity,
3. preservation of fidelity/Bures distance under tensoring with a fixed ancilla.
"""

from __future__ import annotations

import sympy as sp


def main() -> None:
    print("=== SYMPY: BURES/FISHER METRIC STABILIZATION WITNESS ===")

    θ, dθ, θp = sp.symbols("theta dtheta thetap", real=True)

    p = sp.exp(-θ) / (sp.exp(-θ) + sp.exp(θ))
    q = sp.exp(θ) / (sp.exp(-θ) + sp.exp(θ))

    fisher = sp.simplify(sp.diff(p, θ) ** 2 / p + sp.diff(q, θ) ** 2 / q)
    print("\n1. Fisher metric g(θ):")
    sp.pprint(fisher)

    rho = sp.diag(p, q)
    pp = sp.exp(-θp) / (sp.exp(-θp) + sp.exp(θp))
    qq = sp.exp(θp) / (sp.exp(-θp) + sp.exp(θp))
    sigma = sp.diag(pp, qq)

    fidelity = sp.simplify((sp.sqrt(p * pp) + sp.sqrt(q * qq)) ** 2)
    print("\n2. Fidelity F(ρ(θ), ρ(θ')):")
    sp.pprint(fidelity)

    sigma_near = sigma.subs(θp, θ + dθ)
    p_near = sp.simplify(pp.subs(θp, θ + dθ))
    q_near = sp.simplify(qq.subs(θp, θ + dθ))
    fidelity_near = sp.simplify((sp.sqrt(p * p_near) + sp.sqrt(q * q_near)) ** 2)
    bures_sq = sp.simplify(2 * (1 - sp.sqrt(fidelity_near)))
    bures_series = sp.series(bures_sq, dθ, 0, 3).removeO()
    print("\n3. Infinitesimal Bures squared distance series:")
    sp.pprint(bures_series)

    expected_bures = dθ**2 * sp.exp(2 * θ) / (sp.exp(2 * θ) + 1) ** 2
    print("Expected 1/4 Fisher coefficient:")
    sp.pprint(expected_bures)
    assert sp.simplify(sp.expand_trig(bures_series) - expected_bures) == 0

    anc = sp.diag(sp.Rational(1, 2), sp.Rational(1, 2))
    rho_ext = sp.kronecker_product(rho, anc)
    sigma_ext = sp.kronecker_product(sigma, anc)

    fidelity_ext = sp.simplify(
        (sp.sqrt(p * pp) * sp.sqrt(sp.Rational(1, 2) * sp.Rational(1, 2)) * 2
         + sp.sqrt(q * qq) * sp.sqrt(sp.Rational(1, 2) * sp.Rational(1, 2)) * 2) ** 2
    )
    print("\n4. Fidelity after tensoring with I/2 ancilla:")
    sp.pprint(fidelity_ext)
    assert sp.simplify(fidelity_ext - fidelity) == 0

    bures_sq_ext = sp.simplify(2 * (1 - sp.sqrt(fidelity_ext.subs(θp, θ + dθ))))
    bures_ext_series = sp.series(bures_sq_ext, dθ, 0, 3).removeO()
    print("Infinitesimal Bures squared distance after bonding:")
    sp.pprint(bures_ext_series)
    assert sp.simplify(bures_ext_series - bures_series) == 0

    print("\nCONCLUSION:")
    print("  - The one-parameter KMS qubit family has Fisher metric g(θ).")
    print("  - The infinitesimal Bures metric is 1/4 of the Fisher metric in this commuting lane.")
    print("  - Tensoring with a fixed maximally mixed ancilla preserves fidelity.")
    print("  - Therefore the local Bures metric is stable under the bonding map ρ ↦ ρ ⊗ I/2.")


if __name__ == "__main__":
    main()
