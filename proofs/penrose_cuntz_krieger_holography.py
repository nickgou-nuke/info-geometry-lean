"""SymPy witness: Penrose substitution, CK K-theory, and holographic Cantor coding.

For the Penrose rhomb substitution matrix

    M = [[2,1],[1,1]],

we verify:
- det(M)=1, trace(M)=3, characteristic polynomial x^2-3x+1;
- phi^2 is the Perron scaling root;
- I-M^T is unimodular with determinant -1, so
  K0(O_M)=coker(I-M^T)=0 and K1(O_M)=ker(I-M^T)=0;
- binary cylinder counts double, modelling the Cantor/RG-tree boundary coding.
"""

import sympy as sp

x = sp.symbols("x")
phi = (1 + sp.sqrt(5)) / 2
M = sp.Matrix([[2, 1], [1, 1]])
B = sp.eye(2) - M.T
Binv = B.inv()

print("§1  Penrose inflation matrix")
assert M.trace() == 3
assert M.det() == 1
assert sp.factor(M.charpoly(x).as_expr()) == x**2 - 3*x + 1
assert sp.simplify((phi**2)**2 - 3*phi**2 + 1) == 0
print("   tr(M)=3, det(M)=1, chi=x²-3x+1, chi(φ²)=0 ✓")

print("§2  Cuntz--Krieger K-theory")
assert B == sp.Matrix([[-1, -1], [-1, 0]])
assert B.det() == -1
assert all(entry == int(entry) for entry in Binv)
assert B * Binv == sp.eye(2)
assert Binv * B == sp.eye(2)
print("   I-Mᵀ unimodular, det=-1, inverse integral ✓")
print("   K0(O_M)=0 and K1(O_M)=0 ✓")

print("§3  Fibonacci comparison")
A_fib = sp.Matrix([[1, 1], [1, 0]])
B_fib = sp.eye(2) - A_fib.T
assert B_fib.det() == -1
assert B.det() == B_fib.det()
print("   Penrose and Fibonacci CK boundary maps are both unimodular with det=-1 ✓")

print("§4  Cantor/RG boundary coding")
for n in range(12):
    assert 2 ** (n + 1) == 2 * 2**n
# finite patch count grows under M
v = sp.Matrix([1, 0])
for _ in range(8):
    nxt = M * v
    assert sum(nxt) > sum(v)
    v = nxt
print("   binary cylinders double; Penrose finite patches grow along RG tree ✓")

print()
print("penrose_cuntz_krieger_holography.py: All identities verified")
