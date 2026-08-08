"""SymPy witness: n-potent / polynomial symmetry-adapted operators.

Checks that wallpaper/projective symmetry operators are naturally described by
matrix polynomial relations:
- n-potent: A^n=A;
- idempotent, tripotent, nilpotent, involution;
- C4 rotation satisfies C4^4=I;
- glide-like square root of translation satisfies G^2=T;
- Pauli/biquaternion vector satisfies (a·σ)^2=(a·a)I.
"""

import sympy as sp

print("§1  n-potent examples")
I2 = sp.eye(2)
P = sp.diag(1, 0)
Trip = sp.diag(1, -1, 0)
Nil = sp.Matrix([[0, 1], [0, 0]])
Ref = sp.diag(1, -1)
assert P**2 == P
assert Trip**3 == Trip
assert Nil**2 == sp.zeros(2)
assert Ref**2 == I2
print("   idempotent, tripotent, nilpotent, involution relations verified ✓")

print("§2  C4 wallpaper rotation polynomial")
C4 = sp.Matrix([[0, -1], [1, 0]])
assert C4**4 == I2
assert C4**2 == -I2
print("   C4^4=I, minimal polynomial divides x^2+1 ✓")

print("§3  glide as square root of translation")
t = sp.symbols("t", nonzero=True)
G = sp.Matrix([[0, t], [1, 0]])
T = t * I2
assert sp.simplify(G**2 - T) == sp.zeros(2)
print("   G^2=tI: glide/projective operator squares to translation phase ✓")

print("§4  Pauli/biquaternion polynomial closure")
a1, a2, a3, a0 = sp.symbols("a1 a2 a3 a0")
s1 = sp.Matrix([[0, 1], [1, 0]])
s2 = sp.Matrix([[0, -sp.I], [sp.I, 0]])
s3 = sp.Matrix([[1, 0], [0, -1]])
V = a1*s1 + a2*s2 + a3*s3
X = a0*I2 + V
r = a1**2 + a2**2 + a3**2
assert sp.simplify(V**2 - r*I2) == sp.zeros(2)
assert sp.simplify((X - a0*I2)**2 - r*I2) == sp.zeros(2)
print("   (a·σ)^2=(a·a)I, so biquaternions obey quadratic polynomials ✓")

print()
print("polynomial_symmetry_operators.py: All identities verified")
