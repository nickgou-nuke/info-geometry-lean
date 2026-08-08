"""2×2 Jordan block checks inspired by AFP Jordan_Normal_Form.

This is the finite local block lemma: J(λ)=λI+N with N²=0, N≠0,
trace J=2λ, det J=λ².
"""
import sympy as sp

print("§1 Jordan nilpotent block")
lam = sp.symbols("lam")
I = sp.eye(2)
N = sp.Matrix([[0, 1], [0, 0]])
J = sp.Matrix([[lam, 1], [0, lam]])
assert N**2 == sp.zeros(2)
assert N != sp.zeros(2)
assert J == lam * I + N
assert N * J == lam * N
assert J * N == lam * N
assert J**2 == lam**2 * I + 2 * lam * N
e0 = sp.Matrix([1, 0])
e1 = sp.Matrix([0, 1])
assert N * e0 == sp.zeros(2, 1)
assert N * e1 == e0
x0, x1 = sp.symbols("x0 x1")
x = sp.Matrix([x0, x1])
assert N * x == sp.Matrix([x1, 0])
print("   J=λI+N, N²=0, N≠0, JN=NJ=λN, J²=λ²I+2λN ✓")

print("§2 trace/determinant")
assert sp.simplify(J.trace() - 2*lam) == 0
assert sp.simplify(J.det() - lam**2) == 0
assert (J - lam*I)**2 == sp.zeros(2)
assert J - lam*I != sp.zeros(2)
assert J * e0 == lam * e0
assert J * e1 == lam * e1 + e0
for n in range(1, 8):
    assert sp.simplify(J**n - (lam**n * I + n * lam**(n-1) * N)) == sp.zeros(2)
print("   trace(J)=2λ, det(J)=λ², and Jⁿ=λⁿI+nλⁿ⁻¹N for checked n ✓")

print("jordan_block2.py: all identities verified")
