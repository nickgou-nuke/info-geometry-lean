#!/usr/bin/env sage
# -*- coding: utf-8 -*-
"""
Attention = Quantum Fluid: SageMath Verification
"""

print("="*70)
print("SAGEMATH: ATTENTION = QUANTUM FLUID VERIFICATION")
print("="*70)

# 1. Log-Sum-Exp and Softmax Derivatives
print("\n=== 1. Log-Sum-Exp & Softmax ===")
theta = var('theta')
a0, a1, a2 = var('a0 a1 a2')
w0, w1, w2 = var('w0 w1 w2')

Z = w0 * exp(a0 * theta) + w1 * exp(a1 * theta) + w2 * exp(a2 * theta)
F = log(Z)

print(f"Log-partition F(θ) = {F}")

# First derivative
dF = diff(F, theta)
# Softmax expectation
p0 = w0 * exp(a0 * theta) / Z
p1 = w1 * exp(a1 * theta) / Z
p2 = w2 * exp(a2 * theta) / Z
E_a = p0 * a0 + p1 * a1 + p2 * a2

diff_1 = (dF - E_a).simplify_full()
print(f"First derivative gap (dF/dθ - E[a]): {diff_1}")
assert diff_1 == 0, "First derivative check failed!"
print("✓ First derivative: dF/dθ = E_softmax[a]")

# Second derivative
d2F = diff(dF, theta)
E_a2 = p0 * a0^2 + p1 * a1^2 + p2 * a2^2
Var_a = E_a2 - E_a^2

diff_2 = (d2F - Var_a).simplify_full()
print(f"Second derivative gap (d²F/dθ² - Var[a]): {diff_2}")
assert diff_2 == 0, "Second derivative check failed!"
print("✓ Second derivative: d²F/dθ² = Var_softmax[a]")

# 2. Skew-Symmetric (Bivector) Trace Zero
print("\n=== 2. Skew-Symmetric (Bivector) Trace Zero ===")
R = RR
K = matrix(R, [[0, 2, 3], [-2, 0, 5], [-3, -5, 0]])
print("Skew-symmetric matrix K:")
print(K)
print(f"trace(K) = {K.trace()}")
assert K.trace() == 0, "Skew-symmetric matrix trace was not zero!"
print("✓ trace(K) = 0 verified")

print("\n" + "="*70)
print("SAGEMATH VERIFICATION COMPLETE")
print("="*70)
