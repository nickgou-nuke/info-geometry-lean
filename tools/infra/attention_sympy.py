#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Attention = Quantum Fluid: SymPy Verification
"""

from sympy import symbols, exp, log, diff, simplify, Matrix, trace

print("="*70)
print("SYMPY: ATTENTION = QUANTUM FLUID VERIFICATION")
print("="*70)

# 1. Log-Sum-Exp and Softmax Expectation
print("\n=== 1. Log-Sum-Exp & Softmax Expectation ===")
theta = symbols('theta', real=True)
a0, a1, a2 = symbols('a0 a1 a2', real=True)
w0, w1, w2 = symbols('w0 w1 w2', positive=True)

Z = w0 * exp(a0 * theta) + w1 * exp(a1 * theta) + w2 * exp(a2 * theta)
F = log(Z)

print(f"Log-partition function F(θ) = {F}")

# First derivative
dF = diff(F, theta)

# Softmax expectation
p0 = w0 * exp(a0 * theta) / Z
p1 = w1 * exp(a1 * theta) / Z
p2 = w2 * exp(a2 * theta) / Z
E_a = p0 * a0 + p1 * a1 + p2 * a2

diff_1 = simplify(dF - E_a)
print(f"First derivative gap (dF/dθ - E[a]): {diff_1}")
assert diff_1 == 0, "First derivative check failed!"
print("✓ First derivative verified: dF/dθ = E_softmax[a]")

# 2. Second Derivative = Variance
print("\n=== 2. Second Derivative = Variance ===")
d2F = diff(dF, theta)
E_a2 = p0 * a0**2 + p1 * a1**2 + p2 * a2**2
Var_a = E_a2 - E_a**2

diff_2 = simplify(d2F - Var_a)
print(f"Second derivative gap (d²F/dθ² - Var[a]): {diff_2}")
assert diff_2 == 0, "Second derivative check failed!"
print("✓ Second derivative verified: d²F/dθ² = Var_softmax[a]")

# 3. Skew-Symmetric (Bivector) Trace Zero
print("\n=== 3. Skew-Symmetric (Bivector) Trace Zero ===")
K = Matrix([[0, 2, 3], [-2, 0, 5], [-3, -5, 0]])
print("Skew-symmetric matrix K:")
print(K)

tr_K = trace(K)
print(f"trace(K) = {tr_K}")
assert tr_K == 0, "Skew-symmetric matrix trace was not zero!"
print("✓ trace(K) = 0 verified")

print("\n" + "="*70)
print("SYMPY VERIFICATION COMPLETE")
print("="*70)
