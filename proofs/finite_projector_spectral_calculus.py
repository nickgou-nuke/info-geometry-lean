"""Finite projector spectral calculus checks.

Orthogonal idempotents P_i with sum P_i=I diagonalize
H=sum_i eps_i P_i.  Then H P_j=eps_j P_j and H^k=sum_i eps_i^k P_i.
"""
import sympy as sp

print("§1 orthogonal idempotents and diagonal Hamiltonian")
eps = sp.symbols("e0 e1 e2")
P = [
    sp.diag(1, 0, 0),
    sp.diag(0, 1, 0),
    sp.diag(0, 0, 1),
]
I3 = sp.eye(3)
assert sum(P, sp.zeros(3)) == I3
for i in range(3):
    for j in range(3):
        assert P[i] * P[j] == (P[i] if i == j else sp.zeros(3))
H = sum((eps[i] * P[i] for i in range(3)), sp.zeros(3))
print("   P_i P_j=δ_ij P_i and H=Σ eps_i P_i ✓")

print("§2 eigenprojection equations")
for j in range(3):
    assert H * P[j] == eps[j] * P[j]
    assert P[j] * H == eps[j] * P[j]
print("   H P_j=P_j H=eps_j P_j ✓")

print("§3 power spectral theorem")
for k in range(8):
    rhs = sum((eps[i] ** k * P[i] for i in range(3)), sp.zeros(3))
    assert sp.simplify(H ** k - rhs) == sp.zeros(3)
print("   H^k=Σ eps_i^k P_i for k=0..7 ✓")

print("§4 polynomial functional calculus")
x = sp.symbols("x")
f = 7 - 3*x + 5*x**2 + x**5
fH = 7*I3 - 3*H + 5*(H**2) + H**5
rhs = sum((f.subs(x, eps[i]) * P[i] for i in range(3)), sp.zeros(3))
assert sp.simplify(fH - rhs) == sp.zeros(3)
print("   f(H)=Σ f(eps_i)P_i for polynomial f ✓")

print("finite_projector_spectral_calculus.py: all identities verified")
