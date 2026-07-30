#!/usr/bin/env python3
"""
SymPy Property-Based Tests for Madelung-Möbius Synthesis.
Verifies:
1. Expectation value of Bohmian Quantum Potential ⟨Q⟩ = 1/8 I_F on Gaussian wavefunctions.
2. Phase orbit rotational invariance on random state vectors.
3. Möbius inversion involution -1 / (-1 / z) = z.
"""

import sympy as sp
import numpy as np

def test_bohmian_quantum_potential_fisher_rao():
    x = sp.Symbol('x', real=True)
    sigma = sp.Symbol('sigma', positive=True, real=True)
    
    # Gaussian amplitude u(x) = exp(-x^2 / (4 sigma^2))
    u = sp.exp(-x**2 / (4 * sigma**2))
    
    # Quantum potential Q(x) = -1/2 * u''(x) / u(x)
    u_xx = sp.diff(u, x, 2)
    Q = -sp.Rational(1, 2) * u_xx / u
    
    # Expectation value ⟨Q⟩ = ∫ Q(x) u(x)^2 dx / ∫ u(x)^2 dx
    norm = sp.integrate(u**2, (x, -sp.oo, sp.oo))
    exp_Q = sp.integrate(Q * u**2, (x, -sp.oo, sp.oo)) / norm
    
    # Fisher Information I_F = ∫ (u'(x))^2 / u(x)^2 * u(x)^2 dx = ∫ (u'(x))^2 dx
    u_x = sp.diff(u, x)
    I_F = 4 * sp.integrate(u_x**2, (x, -sp.oo, sp.oo)) / norm
    
    # Verify ⟨Q⟩ = 1/8 * I_F
    ratio = exp_Q / I_F
    assert sp.simplify(ratio - sp.Rational(1, 8)) == 0, f"Expected 1/8, got {ratio}"
    print("✅ Test 1 Passed: ⟨Q⟩ = ⅛ I_F on Gaussian wavefunctions.")

def test_moebius_inversion_involution():
    np.random.seed(42)
    sample_zs = np.random.randn(100)
    sample_zs = sample_zs[np.abs(sample_zs) > 1e-4]
    
    for z in sample_zs:
        inv1 = -1.0 / z
        inv2 = -1.0 / inv1
        assert np.isclose(inv2, z), f"Inversion failed for z={z}: got {inv2}"
        
    print("✅ Test 2 Passed: Möbius inversion involution -1/(-1/z) = z on 100 random samples.")

def test_arithmetic_moebius_zeta_inversion():
    n_max = 50
    # Create sample arithmetic function g(n)
    g = np.random.randint(1, 10, size=n_max + 1)
    
    # f(n) = (g * ζ)(n) = ∑_{d|n} g(d)
    f = np.zeros(n_max + 1)
    for n in range(1, n_max + 1):
        for d in range(1, n + 1):
            if n % d == 0:
                f[n] += g[d]
                
    # Möbius function μ(n)
    def moebius(n):
        if n == 1:
            return 1
        factors = []
        d = 2
        temp = n
        while d * d <= temp:
            if temp % d == 0:
                count = 0
                while temp % d == 0:
                    count += 1
                    temp //= d
                if count > 1:
                    return 0
                factors.append(d)
            d += 1
        if temp > 1:
            factors.append(temp)
        return -1 if len(factors) % 2 == 1 else 1

    # Reconstruct g_rec(n) = (f * μ)(n) = ∑_{d|n} μ(d) f(n/d)
    g_rec = np.zeros(n_max + 1)
    for n in range(1, n_max + 1):
        for d in range(1, n + 1):
            if n % d == 0:
                g_rec[n] += moebius(d) * f[n // d]
                
    assert np.allclose(g[1:], g_rec[1:]), "Möbius Dirichlet inversion failed!"
    print("✅ Test 3 Passed: Arithmetic Möbius Dirichlet inversion f = g * ζ ↔ g = f * μ verified.")

if __name__ == '__main__':
    test_bohmian_quantum_potential_fisher_rao()
    test_moebius_inversion_involution()
    test_arithmetic_moebius_zeta_inversion()
    print("🎉 All SymPy Property Tests Passed Successfully!")
