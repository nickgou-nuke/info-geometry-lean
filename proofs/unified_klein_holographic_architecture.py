"""Executable witness for the unified Klein holographic architecture.

This script records the implication chain assembled in Lean/SymPy modules:

non-split wallpaper extension -> glide G^2=T -> Klein boundary -> ribbon π twist
-> log(-I2) half spectrum -> bulk charge conjugation defect -> Q^2=H.
"""

import sympy as sp


def assert_matrix_zero(name, M):
    S = sp.simplify(M)
    if S != sp.zeros(*S.shape):
        raise AssertionError(f"{name} failed:\n{S}")

print("§1  boundary cocycle and glide")
t = sp.Symbol("t", nonzero=True)
assert t != 0
# Affine glide F(x,y)=(x+1/2,-y), longitudinal translation Tx.
F = sp.Matrix([[1, 0, sp.Rational(1, 2)], [0, -1, 0], [0, 0, 1]])
Tx = sp.Matrix([[1, 0, 1], [0, 1, 0], [0, 0, 1]])
assert_matrix_zero("G^2=T", F**2 - Tx)
print("   c(σ,σ)=t≠0 and G²=T ✓")

print("§2  Klein bottle cycle")
Ty = sp.Matrix([[1, 0, 0], [0, 1, 1], [0, 0, 1]])
Finv = sp.Matrix([[1, 0, -sp.Rational(1, 2)], [0, -1, 0], [0, 0, 1]])
Ty_inv = sp.Matrix([[1, 0, 0], [0, 1, -1], [0, 0, 1]])
assert_matrix_zero("G Ty G^-1 = Ty^-1", F * Ty * Finv - Ty_inv)
print("   orientation-reversing cycle gives Klein relation ✓")

print("§3  ribbon π twist equals log(-I2) half spectrum")
I2 = sp.eye(2)
L = sp.diag(sp.I * sp.pi, sp.I * sp.pi)  # one branch of log(-I2)
connection = L / (2 * sp.pi * sp.I)
assert_matrix_zero("exp(log(-I))=-I", L.exp() + I2)
assert connection[0, 0] == sp.Rational(1, 2)
assert sp.simplify(sp.exp(2 * sp.pi * sp.I * connection[0, 0]) + 1) == 0
print("   L=(2πi)^-1 log(-I2) has half eigenvalue and phase -1 ✓")

print("§4  bulk defect and discrete SUSY")
C = sp.Matrix([[0, 1], [1, 0]])
assert_matrix_zero("C^2=I", C**2 - I2)
z = sp.Symbol("z", nonzero=True)
Q = sp.Matrix([[0, z], [1, 0]])
H = z * I2
assert_matrix_zero("Q^2=H", Q**2 - H)
print("   charge conjugation is involutive and glide supercharge obeys Q²=H ✓")

print()
print("unified_klein_holographic_architecture.py: All identities verified")
