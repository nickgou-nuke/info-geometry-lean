"""SymPy witness: soldering forms, spin connection, Bogoliubov frame bundle.

Algebraic cores:
- Pauli soldering maps vectors -> Hermitian 2x2 matrices with Minkowski determinant.
- Tetrad/soldering form builds spacetime metric g = e^T eta e.
- A 2D spin connection curvature F=dω+ω∧ω; for an abelian SO(1,1) boost atom, ω∧ω=0.
- A Bogoliubov frame preserves the bosonic symplectic form J iff B^T J B=J.
"""

import sympy as sp

print("§1  Pauli soldering form")
t, x, y, z, lam = sp.symbols("t x y z lam", real=True)
I2 = sp.eye(2)
s1 = sp.Matrix([[0, 1], [1, 0]])
s2 = sp.Matrix([[0, -sp.I], [sp.I, 0]])
s3 = sp.Matrix([[1, 0], [0, -1]])
X = t*I2 + x*s1 + y*s2 + z*s3
assert sp.expand(X.det() - (t**2 - x**2 - y**2 - z**2)) == 0
assert sp.expand((lam*I2 - X).det() - ((lam-t)**2 - (x**2+y**2+z**2))) == 0
print("   solder(v)=v^μσ_μ has det=Minkowski and lightcone charpoly ✓")

print("§2  tetrad metric from soldering form")
e = sp.diag(sp.symbols("e0", nonzero=True), sp.symbols("e1", nonzero=True), sp.symbols("e2", nonzero=True), sp.symbols("e3", nonzero=True))
eta = sp.diag(1, -1, -1, -1)
g = e.T * eta * e
assert g == sp.diag(e[0,0]**2, -e[1,1]**2, -e[2,2]**2, -e[3,3]**2)
print("   g_{μν}=e^a_μ η_ab e^b_ν ✓")

print("§3  spin connection curvature atom")
u, vcoord = sp.symbols("u v")
a, b = sp.Function("a"), sp.Function("b")
# SO(1,1) boost generator squares to +1 but bracket with itself is zero in 1D Lie algebra.
K = sp.Matrix([[0, 1], [1, 0]])
omega_u = a(u, vcoord)*K
omega_v = b(u, vcoord)*K
curv_uv = sp.diff(omega_v, u) - sp.diff(omega_u, vcoord) + omega_u*omega_v - omega_v*omega_u
expected = (sp.diff(b(u, vcoord), u) - sp.diff(a(u, vcoord), vcoord))*K
assert sp.simplify(curv_uv - expected) == sp.zeros(2)
print("   F_uv=∂uωv-∂vωu+[ωu,ωv]; abelian boost atom has zero commutator ✓")

print("§4  Bogoliubov frame symplectic preservation")
ch, sh = sp.symbols("ch sh")
B = sp.Matrix([[ch, sh], [sh, ch]])
J = sp.Matrix([[1, 0], [0, -1]])
assert sp.simplify(B.T*J*B - (ch**2-sh**2)*J) == sp.zeros(2)
print("   B^T J B=(ch²-sh²)J, hence preserves CAR/Krein form when ch²-sh²=1 ✓")

print()
print("soldering_spin_connection_bogoliubov.py: All identities verified")
