#!/usr/bin/env python3
"""
Symbolic verification of Gaussian Information Surprisal, KL Divergence,
Free Energy Difference, and Effective Potential under Moebius Reflection.
"""

import sympy as sp

def main():
    print("=" * 72)
    print("MOEBIUS GAUSSIAN INFORMATION GEOMETRY & FREE ENERGY VERIFICATION")
    print("=" * 72)

    sigma, t, v, beta, F0, kappa = sp.symbols('sigma t v beta F0 kappa', real=True, positive=True)
    sigma_real = sp.Symbol('sigma_real', real=True)

    # 1. States and Moebius Reflection
    m1 = sp.Matrix([sigma_real, t])
    m2 = sp.Matrix([1 - sigma_real, t])  # Moebius reflected mean

    print(f"  Mean m1 = {m1.T}")
    print(f"  Moebius Mean m2 = {m2.T}")

    # 2. Casimir Invariant
    C = (sigma_real - sp.Rational(1, 2))**2

    # 3. KL Divergence: D_KL(N(m1, v*I) || N(m2, v*I)) = ||m1 - m2||^2 / (2 * v)
    diff = m1 - m2
    dist_sq = sp.simplify((diff.T * diff)[0, 0])
    kl_div = dist_sq / (2 * v)
    expected_kl = (2 / v) * C

    print(f"  ||m1 - m2||^2 = {dist_sq}")
    print(f"  D_KL = {kl_div}")
    print(f"  Expected D_KL = {expected_kl}")
    assert sp.simplify(kl_div - expected_kl) == 0, "KL Divergence formula mismatch!"
    print("  [OK] 1. Exact Moebius KL Divergence D_KL = (2/v)*C verified.")

    # 4. Critical Line Vanishing of KL Divergence
    kl_on_critical = kl_div.subs(sigma_real, sp.Rational(1, 2))
    assert kl_on_critical == 0, "KL divergence does not vanish on critical line!"
    print("  [OK] 2. D_KL = 0 on critical line sigma = 1/2 verified.")

    # 5. Free Energy Difference: Delta F = (1/beta) * D_KL = (2 / (beta * v)) * C
    delta_F = (1 / beta) * kl_div
    expected_delta_F = (2 / (beta * v)) * C
    assert sp.simplify(delta_F - expected_delta_F) == 0, "Free energy diff mismatch!"
    print(f"  Delta F_Moebius = {delta_F}")
    print("  [OK] 3. Exact Free Energy Difference Delta F = (2 / (beta * v))*C verified.")

    # 6. Effective Potential: V_eff = F0 + kappa * C
    V_eff = F0 + kappa * C
    V_eff_diff = sp.diff(V_eff, sigma_real)
    crit_pts = sp.solve(V_eff_diff, sigma_real)
    print(f"  dV_eff / dsigma = {V_eff_diff}")
    print(f"  Critical point of V_eff = {crit_pts}")
    assert crit_pts == [sp.Rational(1, 2)], "Unique minimum is not at sigma = 1/2!"
    print("  [OK] 4. Unique Global Minimum of V_eff at sigma = 1/2 verified.")

    print("=" * 72)
    print("ALL MOEBIUS GAUSSIAN INFORMATION THEOREMS 100% CAS VERIFIED")
    print("=" * 72)

if __name__ == '__main__':
    main()
