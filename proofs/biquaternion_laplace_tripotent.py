"""SymPy witness: biquaternion Laplace resolvent and tripotent scale boundary.

Checks:
1. For X=a0 I + a·σ, the resolvent identity
   (sI-X)^-1 = ((s-a0)I + a·σ)/((s-a0)^2-a·a).
2. det(exp(X))=exp(tr X), so exp(X)=0 has no finite solution.
3. Scale flow X(r)=-r I has exp(X(r))->0 as r->∞.
4. Tripotent T=diag(1,-1,0) has resolvent determinant poles at s=1,-1,0.
5. Resolvent tends to zero as s->∞.
"""

import sympy as sp


def assert_matrix_zero(name, M):
    S = sp.simplify(M)
    if S != sp.zeros(*S.shape):
        raise AssertionError(f"{name} failed:\n{S}")

print("§1  Biquaternion resolvent identity")
s, a0, a1, a2, a3 = sp.symbols("s a0 a1 a2 a3")
I2 = sp.eye(2)
s1 = sp.Matrix([[0, 1], [1, 0]])
s2 = sp.Matrix([[0, -sp.I], [sp.I, 0]])
s3 = sp.Matrix([[1, 0], [0, -1]])
T = a1*s1 + a2*s2 + a3*s3
X = a0*I2 + T
A = s - a0
v2 = a1**2 + a2**2 + a3**2
num = A*I2 + T
den = A**2 - v2
assert_matrix_zero("(sI-X)*num = den I", (s*I2 - X) * num - den * I2)
assert_matrix_zero("num*(sI-X) = den I", num * (s*I2 - X) - den * I2)
print("   closed-form (sI-X)^-1 numerator/denominator verified ✓")

print("§2  finite matrix exponential cannot be zero")
trX = sp.trace(X)
# Symbolic determinant of exp is hard for symbolic X; verify through eigenvalue formula.
lam1 = a0 + sp.sqrt(v2)
lam2 = a0 - sp.sqrt(v2)
assert sp.simplify(sp.exp(lam1) * sp.exp(lam2) - sp.exp(2*a0)) == 0
assert trX == 2*a0
print("   det(exp X)=exp(tr X)=exp(2a0), never zero for finite a0 ✓")

print("§3  zero monodromy as infinite-scale limit")
r = sp.symbols("r", positive=True)
flow = sp.exp(-r) * I2
assert sp.limit(flow[0,0], r, sp.oo) == 0
assert sp.limit(flow[1,1], r, sp.oo) == 0
print("   exp(-r I)->0 as r→∞ ✓")

print("§4  tripotent resolvent poles")
T3 = sp.diag(1, -1, 0)
assert_matrix_zero("T^3=T", T3**3 - T3)
S = s*sp.eye(3) - T3
detS = sp.factor(S.det())
assert detS == s*(s - 1)*(s + 1)
print("   det(sI-T)=s(s-1)(s+1): poles at -1,0,+1 ✓")

print("§5  resolvent vanishes at conformal infinity")
R = S.inv()
for i in range(3):
    assert sp.limit(R[i,i], s, sp.oo) == 0
print("   (sI-T)^-1 -> 0 as s→∞ ✓")

print()
print("biquaternion_laplace_tripotent.py: All identities verified")
