#!/usr/bin/env python3
"""
Symbolic verification of the Onsager-Casimir dissipation bracket
and its Moebius reflection invariance in the 2D Hestenes-Krein plane.
"""

import sympy as sp

def main():
    print("=" * 72)
    print("ONSAGER-CASIMIR METRIPLECTIC BRACKET & MOEBIUS SYMMETRY VERIFICATION")
    print("=" * 72)

    sigma, t, gamma_fisher = sp.symbols('sigma t gamma_fisher', real=True)

    # 1. State and Casimir Invariant
    C = (sigma - sp.Rational(1, 2))**2
    grad_C = (sp.diff(C, sigma), sp.diff(C, t))

    print(f"  Casimir C(s) = {C}")
    print(f"  grad(C) = {grad_C}")
    assert grad_C == (2 * (sigma - sp.Rational(1, 2)), 0), "Casimir gradient mismatch!"
    print("  [OK] 1. Exact Casimir Gradient verified.")

    # 2. Onsager Bracket: (F, G)_M = gamma_fisher * (gradF . gradG)
    def onsager_bracket(grad_F, grad_G):
        return gamma_fisher * (grad_F[0] * grad_G[0] + grad_F[1] * grad_G[1])

    # Casimir self-dissipation
    casimir_dissipation = onsager_bracket(grad_C, grad_C)
    expected_dissipation = 4 * gamma_fisher * C
    assert sp.simplify(casimir_dissipation - expected_dissipation) == 0, "Dissipation formula mismatch!"
    print(f"  (C, C)_M = {casimir_dissipation} = 4 * gamma_fisher * C")
    print("  [OK] 2. Exact Casimir Dissipation (C, C)_M = 4 * gamma_fisher * C verified.")

    # 3. Critical Line Vanishing
    dissipation_at_half = casimir_dissipation.subs(sigma, sp.Rational(1, 2))
    assert dissipation_at_half == 0, "Dissipation does not vanish on the critical line!"
    print("  [OK] 3. Dissipation Vanishes on Critical Line sigma = 1/2 verified.")

    # 4. Moebius Reflection Invariance: sigma -> 1 - sigma
    C_moebius = C.subs(sigma, 1 - sigma)
    assert sp.simplify(C_moebius - C) == 0, "Casimir is not Moebius invariant!"
    print("  [OK] 4. Casimir Moebius Invariance C(1 - sigma, t) = C(sigma, t) verified.")

    grad_C_moebius = (sp.diff(C_moebius, sigma), sp.diff(C_moebius, t))
    dissipation_moebius = onsager_bracket(grad_C_moebius, grad_C_moebius)
    assert sp.simplify(dissipation_moebius - casimir_dissipation) == 0, "Onsager bracket not Moebius invariant!"
    print("  [OK] 5. Onsager Dissipation Moebius Invariance verified.")

    print("=" * 72)
    print("ALL ONSAGER-CASIMIR-MOEBIUS THEOREMS 100% CAS VERIFIED")
    print("=" * 72)

if __name__ == '__main__':
    main()
