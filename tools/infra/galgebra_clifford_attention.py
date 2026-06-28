#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Attention = Quantum Fluid: GAlgebra + Clifford Verification
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
print("ATTENTION = QUANTUM FLUID: GEOMETRIC ALGEBRA VERIFICATION")
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
print("✓ Skew-adjointness analogue verified: J~ = -J")

# Inner product of any vector v with J*v vanishes
v = symbols('v1') * e1 + symbols('v2') * e2
Jv = J * v
g_v_Jv = (v * Jv).grade(0)
g_val = g_v_Jv.obj
print(f"g(v, Jv) = {simplify(g_val)}")
assert simplify(g_val) == 0, "Kahler check failed!"
print("✓ Orthogonality of flow verified: g(v, Jv) = 0")

print("\n" + "="*70)
print("GEOMETRIC ALGEBRA VERIFICATION COMPLETE")
print("="*70)
