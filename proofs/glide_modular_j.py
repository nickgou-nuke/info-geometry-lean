"""SymPy witness: glide as modular conjugation J.

Tomita modular conjugation satisfies the inversion relation
    J Δ J = Δ^{-1}
which mirrors the Klein glide relation
    G T G^{-1} = T^{-1}.
This witness uses 2x2 matrices: J is the swap matrix and Δ=diag(r,1/r).
"""

import sympy as sp

print("§1  Modular J inverts the modular operator")
r = sp.symbols("r", nonzero=True)
J = sp.Matrix([[0, 1], [1, 0]])
Delta = sp.diag(r, 1/r)
assert J**2 == sp.eye(2)
assert sp.simplify(J * Delta * J - Delta.inv()) == sp.zeros(2)
print("   J²=1 and J Δ J=Δ^{-1} ✓")

print("§2  Modular flow reversal")
n = sp.symbols("n", integer=True)
Delta_n = sp.diag(r**n, r**(-n))
Delta_minus_n = sp.diag(r**(-n), r**n)
assert sp.simplify(J * Delta_n * J - Delta_minus_n) == sp.zeros(2)
print("   J Δⁿ J=Δ^{-n}: modular time reversal ✓")

print("§3  Same algebra as Klein glide")
G = J
T = Delta
klein_word = sp.simplify(G * T * G * T - sp.eye(2))
assert klein_word == sp.zeros(2)
print("   G T G^{-1} T=1 with G=J: glide is modular conjugation ✓")

print()
print("glide_modular_j.py: All identities verified")
