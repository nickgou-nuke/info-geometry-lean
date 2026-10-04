#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Check a small Euclidean Clifford-algebra bivector identity.

This example is independent of transformer attention and fluid dynamics.
"""

try:
    from galgebra.ga import Ga
    from sympy import symbols, simplify
    print("GAlgebra available ✓")
except ImportError:
    print("GAlgebra not available, installing...")
    import subprocess
    subprocess.check_call(['pip', 'install', 'galgebra'])
    from galgebra.ga import Ga
    from sympy import symbols, simplify

print("="*70)
print("GEOMETRIC ALGEBRA: INDEPENDENT BIVECTOR IDENTITIES")
print("="*70)

# Create 2D geometric algebra
ga2 = Ga('e_1 e_2', g=[1, 1])
e1, e2 = ga2.mv()

# J = e1 ∧ e2 represents complex structure (bivector)
J = e1 * e2
print(f"Bivector J = {J}")

# Verify J is skew-adjoint (transpose/reversal matches negative)
J_rev = J.rev()
print(f"Reversal of J: J~ = {J_rev}")
assert J_rev == -J, "Bivector reversal (skew-adjointness) check failed!"
print("✓ Reversal identity in this Clifford algebra: J~ = -J")

# Inner product of any vector v with J*v vanishes
v = symbols('v1') * e1 + symbols('v2') * e2
Jv = J * v
g_v_Jv = (v * Jv).grade(0)
g_val = g_v_Jv.obj
print(f"g(v, Jv) = {simplify(g_val)}")
assert simplify(g_val) == 0, "Kahler check failed!"
print("✓ Scalar part of v*(J*v) vanishes in this example")

print("\n" + "="*70)
print("INDEPENDENT GEOMETRIC ALGEBRA CHECK COMPLETE")
print("="*70)
