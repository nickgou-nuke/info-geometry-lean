#!/usr/bin/env python3
"""
Bogoliubov Covariant Mellin-Krein Quantization CAS Verification.

This script verifies:
1. One-mode / two-mode SU(1,1) Bogoliubov transformations:
   alpha = exp(i phi) cosh(r), beta = exp(i psi) sinh(r)
   |alpha|^2 - |beta|^2 = 1.
2. Poincare disk coordinate z = beta / bar(alpha) with |z| = tanh(r) < 1,
   r = artanh(|z|) = 1/2 ln((1+|z|)/(1-|z|)).
3. Mode operator B_n(u, t) = R_n(t) * B_n(u):
   r_n(u) = u ln(n), theta_n(t) = t ln(n)
   det(B_n(u, t)) = 1, (B_n(u, t))^{-1} = B_n(-u) * R_n(-t).
4. Critical line boost quenching:
   u = 0 => B_n(0, t) = diag(e^{-i t ln n}, e^{i t ln n}) (pure compact rotor).
5. su(1,1) two-mode algebra:
   [K_0, K_+] = K_+, [K_0, K_-] = -K_-, [K_+, K_-] = 2 K_0.
6. Covariant complex structure transformation:
   J_u = B(u) J_0 B(u)^{-1} with J_0 = [[0, -1], [1, 0]], J_u^2 = -I.
"""

import sys
import sympy as sp

def test_bogoliubov_su11_norm():
    print("[1] Testing SU(1,1) Bogoliubov Norm Invariance...")
    r = sp.symbols('r', real=True, positive=True)
    phi, psi = sp.symbols('phi psi', real=True)
    alpha = sp.exp(sp.I * phi) * sp.cosh(r)
    beta = sp.exp(sp.I * psi) * sp.sinh(r)
    
    norm_diff = sp.simplify(sp.Abs(alpha)**2 - sp.Abs(beta)**2)
    assert norm_diff == 1, f"Expected 1, got {norm_diff}"
    
    z = beta / sp.conjugate(alpha)
    abs_z = sp.simplify(sp.Abs(z))
    assert sp.simplify(abs_z - sp.tanh(r)) == 0, f"Expected tanh(r), got {abs_z}"
    print("    -> SU(1,1) norm |alpha|^2 - |beta|^2 = 1 and |z| = tanh(r) verified.")

def test_mellin_bogoliubov_matrix():
    print("[2] Testing Mellin-Bogoliubov Matrix Group Laws...")
    u, t, n = sp.symbols('u t n', real=True, positive=True)
    
    r_n = u * sp.log(n)
    theta_n = t * sp.log(n)
    
    B_u = sp.Matrix([
        [sp.cosh(r_n), sp.sinh(r_n)],
        [sp.sinh(r_n), sp.cosh(r_n)]
    ])
    
    R_t = sp.Matrix([
        [sp.exp(-sp.I * theta_n), 0],
        [0, sp.exp(sp.I * theta_n)]
    ])
    
    B_ut = R_t * B_u
    
    det_B = sp.simplify(B_ut.det())
    assert det_B == 1, f"Expected det = 1, got {det_B}"
    
    # Inversion: B_ut^{-1} = B_n(-u) * R_n(-t)
    r_neg = (-u) * sp.log(n)
    theta_neg = (-t) * sp.log(n)
    
    B_u_inv = sp.Matrix([
        [sp.cosh(r_neg), sp.sinh(r_neg)],
        [sp.sinh(r_neg), sp.cosh(r_neg)]
    ])
    R_t_inv = sp.Matrix([
        [sp.exp(-sp.I * theta_neg), 0],
        [0, sp.exp(sp.I * theta_neg)]
    ])
    
    B_ut_inv = B_u_inv * R_t_inv
    
    prod1 = sp.simplify(B_ut_inv * B_ut)
    prod2 = sp.simplify(B_ut * B_ut_inv)
    assert prod1 == sp.eye(2), f"Expected Identity, got {prod1}"
    assert prod2 == sp.eye(2), f"Expected Identity, got {prod2}"
    
    # Critical line u = 0 quenching
    B_0t = sp.simplify(B_ut.subs(u, 0))
    expected_rotor = sp.Matrix([
        [sp.exp(-sp.I * theta_n), 0],
        [0, sp.exp(sp.I * theta_n)]
    ])
    assert B_0t == expected_rotor, f"Expected {expected_rotor}, got {B_0t}"
    print("    -> Mellin-Bogoliubov group inverse (B_u^{-1} R_t^{-1}) and u=0 boost quenching verified.")

def test_su11_lie_algebra():
    print("[3] Testing su(1,1) Lie Algebra Commutation Relations...")
    K0 = sp.Matrix([[sp.Rational(1, 2), 0], [0, sp.Rational(-1, 2)]])
    Kp = sp.Matrix([[0, 1], [0, 0]])
    Km = sp.Matrix([[0, 0], [1, 0]])
    
    comm_0p = sp.simplify(K0 * Kp - Kp * K0)
    comm_0m = sp.simplify(K0 * Km - Km * K0)
    comm_pm = sp.simplify(Kp * Km - Km * Kp)
    
    assert comm_0p == Kp, f"[K0, K+] expected K+, got {comm_0p}"
    assert comm_0m == -Km, f"[K0, K-] expected -K-, got {comm_0m}"
    assert comm_pm == 2 * K0, f"[K+, K-] expected 2 K0, got {comm_pm}"
    print("    -> [K0, K_pm] = pm K_pm and [K+, K-] = 2 K0 verified.")

def test_complex_structure_transport():
    print("[4] Testing Covariant Complex Structure Polarization Transport...")
    r = sp.symbols('r', real=True)
    J0 = sp.Matrix([[0, -1], [1, 0]])
    assert J0**2 == -sp.eye(2)
    
    B = sp.Matrix([[sp.cosh(r), sp.sinh(r)], [sp.sinh(r), sp.cosh(r)]])
    B_inv = sp.Matrix([[sp.cosh(r), -sp.sinh(r)], [-sp.sinh(r), sp.cosh(r)]])
    
    Jr = sp.simplify(B * J0 * B_inv)
    Jr_sq = sp.simplify(Jr * Jr)
    assert Jr_sq == -sp.eye(2), f"Expected Jr^2 = -I, got {Jr_sq}"
    
    assert sp.simplify(Jr.subs(r, 0)) == J0
    print("    -> Complex structure J_r^2 = -I and J_0 recovery at r=0 verified.")

def main():
    print("=" * 72)
    print("BOGOLIUBOV COVARIANT MELLIN-KREIN QUANTIZATION CAS VERIFICATION")
    print("=" * 72)
    test_bogoliubov_su11_norm()
    test_mellin_bogoliubov_matrix()
    test_su11_lie_algebra()
    test_complex_structure_transport()
    print("=" * 72)
    print("ALL BOGOLIUBOV COVARIANT MELLIN-KREIN INVARIANTS 100% CAS VERIFIED")
    print("=" * 72)

if __name__ == "__main__":
    main()
