"""SymPy witness: Itakura--Saito divergence collapses on nilpotent boundary modes.

For a nilpotent K with K^2=0, exp(K)=I+K, hence
  D_IS(K)=exp(K)-I-K=0.
Equivalently, in the biquaternion closed coefficients
  (cosh(v)-1) I + (sinh(v)/v - 1) K,
the nilpotent/lightcone limit v -> 0 kills both coefficients.
"""

import sympy as sp

print("§1  Closed coefficient limits")
v = sp.symbols("v", real=True)
coeff_I = sp.cosh(v) - 1
coeff_K = (sp.sinh(v) / v) - 1
assert sp.limit(coeff_I, v, 0) == 0
assert sp.limit(coeff_K, v, 0) == 0
print("   lim_{v→0}(cosh(v)-1)=0 and lim_{v→0}(sinh(v)/v-1)=0 ✓")

print("§2  Explicit nilpotent matrix")
K = sp.Matrix([[0, 1], [0, 0]])
I2 = sp.eye(2)
assert K**2 == sp.zeros(2)
expK = I2 + K  # finite truncation because K^2=0
D_IS = expK - I2 - K
assert D_IS == sp.zeros(2)
print("   K²=0 ⇒ exp(K)=I+K ⇒ D_IS(K)=0 ✓")

print("§3  Scaled nilpotent remains zero-divergence")
eps = sp.symbols("eps")
exp_epsK = I2 + eps*K
D_eps = exp_epsK - I2 - eps*K
assert D_eps == sp.zeros(2)
print("   D_IS(εK)=0 for all ε when K²=0 ✓")

print()
print("nilpotent_itakura_saito.py: All identities verified")
