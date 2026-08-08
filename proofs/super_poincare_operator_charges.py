"""Finite matrix checks for operator-valued super-Poincare charge lemmas."""
import sympy as sp

print("§1 chiral nilpotent supercharges")
z = sp.symbols("z")
Qp = sp.Matrix([[0, 1], [0, 0]])
Qm = sp.Matrix([[0, 0], [1, 0]])
D = Qp + Qm
anti = Qp * Qm + Qm * Qp
assert Qp * Qp == sp.zeros(2)
assert Qm * Qm == sp.zeros(2)
assert D * D == anti
print("   Q+²=Q-²=0 implies (Q+ + Q-)²={Q+,Q-} ✓")

print("§2 central charge as operator")
Z = z * sp.eye(2)
X = sp.Matrix([[1, 2], [3, 5]])
assert Z * X - X * Z == sp.zeros(2)
assert Z * Qp - Qp * Z == sp.zeros(2)
assert Z * Qm - Qm * Z == sp.zeros(2)
print("   Z is an operator commuting with observables/supercharges ✓")

print("§3 momentum operator from mixed anticommutator")
P = anti
assert D * D == P
assert P == sp.eye(2)
print("   P={Q+,Q-}=Dχ² in the 2×2 chiral CAR representation ✓")

print("super_poincare_operator_charges.py: all identities verified")
