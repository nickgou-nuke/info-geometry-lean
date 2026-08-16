#!/usr/bin/env python3
"""
Symbolic verification of the Radon-Nikodym Information Transport,
Fisher Natural Gradient, and Moebius Commutation in the Hestenes-Krein Plane.
"""

import sympy as sp

def main():
    print("=" * 72)
    print("RADON-NIKODYM INFORMATION TRANSPORT & FISHER NATURAL GRADIENT")
    print("=" * 72)

    sigma, t, kappa, m, F0, tau, a = sp.symbols('sigma t kappa m F0 tau a', real=True, positive=True)
    sigma_real, t_real = sp.symbols('sigma_real t_real', real=True)

    # 1. State and Potentials
    C = (sigma_real - sp.Rational(1, 2))**2
    F = F0 + kappa * C + sp.Rational(1, 2) * m**2 * t_real**2

    grad_F = sp.Matrix([sp.diff(F, sigma_real), sp.diff(F, t_real)])
    g_Fisher = sp.Matrix([[2 * kappa, 0], [0, m**2]])
    g_inv = g_Fisher.inv()

    # Natural Gradient: tilde_grad(F) = g_inv * grad_F
    nat_grad = g_inv * grad_F
    expected_nat_grad = sp.Matrix([sigma_real - sp.Rational(1, 2), t_real])

    print(f"  grad(F) = {grad_F.T}")
    print(f"  g_Fisher^(-1) =\n{g_inv}")
    print(f"  Natural Gradient = {nat_grad.T}")
    assert sp.simplify(nat_grad - expected_nat_grad) == sp.Matrix([0, 0]), "Natural gradient mismatch!"
    print("  [OK] 1. Exact Natural Gradient tilde_grad(F) = (sigma - 1/2, t) verified.")

    # 2. Radon-Nikodym Transport Operator: T_RN(a)(sigma, t) = (1/2 + (sigma - 1/2)*a, t*a)
    s_transport = sp.Matrix([sp.Rational(1, 2) + (sigma_real - sp.Rational(1, 2)) * a, t_real * a])

    # Casimir under RN transport
    C_transport = (s_transport[0] - sp.Rational(1, 2))**2
    expected_C_transport = a**2 * C
    assert sp.simplify(C_transport - expected_C_transport) == 0, "Casimir under transport mismatch!"
    print(f"  C(T_RN(s)) = {C_transport} = a^2 * C(s)")
    print("  [OK] 2. Exact Casimir Contraction C(T_RN(s)) = a^2 * C(s) verified.")

    # 3. Moebius Commutation with RN Transport
    # M(s) = (1 - sigma, t)
    # T_RN(M(s)) = (1/2 + (1 - sigma - 1/2)*a, t*a) = (1/2 - (sigma - 1/2)*a, t*a)
    # M(T_RN(s)) = (1 - (1/2 + (sigma - 1/2)*a), t*a) = (1/2 - (sigma - 1/2)*a, t*a)
    T_M_s = sp.Matrix([sp.Rational(1, 2) + (1 - sigma_real - sp.Rational(1, 2)) * a, t_real * a])
    M_T_s = sp.Matrix([1 - s_transport[0], s_transport[1]])
    assert sp.simplify(T_M_s - M_T_s) == sp.Matrix([0, 0]), "Moebius does not commute with RN transport!"
    print("  [OK] 3. Exact Moebius Commutation M o T_RN = T_RN o M verified.")

    # 4. Fisher Distance Decay
    # dist_g^2(s) = 2*kappa*(sigma - 1/2)^2 + m^2 * t^2
    dist_sq_orig = 2 * kappa * (sigma_real - sp.Rational(1, 2))**2 + m**2 * t_real**2
    dist_sq_trans = 2 * kappa * (s_transport[0] - sp.Rational(1, 2))**2 + m**2 * s_transport[1]**2
    assert sp.simplify(dist_sq_trans - a**2 * dist_sq_orig) == 0, "Fisher distance decay mismatch!"
    print("  [OK] 4. Exact Fisher Distance Decay dist^2(T_RN(s)) = a^2 * dist^2(s) verified.")

    print("=" * 72)
    print("ALL RADON-NIKODYM TRANSPORT THEOREMS 100% CAS VERIFIED")
    print("=" * 72)

if __name__ == '__main__':
    main()
