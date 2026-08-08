"""SymPy witness: modular/RG scaling flow on Zorn split-octonion matrices.

Zorn element X=(a,u,v,b) represents [[a,u],[v,b]].  For the diagonal
boost D=diag(exp(k eps), exp(-k eps)), the conjugation D*X*D^{-1} gives

  a -> a,        b -> b,
  u -> exp( 2 k eps) u,
  v -> exp(-2 k eps) v.

Thus diagonal elements are strict fixed points; upper/lower pure off-diagonal
states are nilpotent and form repeller/attractor directions of the scaling flow.
"""

import sympy as sp


def dot(u, v):
    return sum(ui*vi for ui, vi in zip(u, v))


def cross(u, v):
    return [u[1]*v[2]-u[2]*v[1], u[2]*v[0]-u[0]*v[2], u[0]*v[1]-u[1]*v[0]]


def zorn_mul(X, Y):
    a, u, v, b = X
    c, w, z, d = Y
    return (
        sp.simplify(a*c + dot(u, z)),
        [sp.simplify(a*w[i] + d*u[i] - cross(v, z)[i]) for i in range(3)],
        [sp.simplify(c*v[i] + b*z[i] + cross(u, w)[i]) for i in range(3)],
        sp.simplify(b*d + dot(v, w)),
    )


print("§1  Diagonal modular scaling flow")
a, b, eps, k = sp.symbols("a b eps k", positive=True)
u1, u2, u3, v1, v2, v3 = sp.symbols("u1 u2 u3 v1 v2 v3")
u = [u1, u2, u3]
v = [v1, v2, v3]
X = (a, u, v, b)
alpha = sp.exp(k*eps)
beta = sp.exp(-k*eps)
D = (alpha, [0,0,0], [0,0,0], beta)
Dinv = (1/alpha, [0,0,0], [0,0,0], 1/beta)
flow = zorn_mul(zorn_mul(D, X), Dinv)
expected = (a, [sp.exp(2*k*eps)*ui for ui in u], [sp.exp(-2*k*eps)*vi for vi in v], b)
assert all(sp.simplify(flow[0] - expected[0]) == 0 for _ in [0])
assert all(sp.simplify(flow[1][i] - expected[1][i]) == 0 for i in range(3))
assert all(sp.simplify(flow[2][i] - expected[2][i]) == 0 for i in range(3))
assert sp.simplify(flow[3] - expected[3]) == 0
print("   D X D^{-1}: u scales e^{+2kε}, v scales e^{-2kε}; diagonals fixed ✓")

print("§2  Strict fixed diagonal Cartan sector")
Diag = (a, [0,0,0], [0,0,0], b)
assert zorn_mul(zorn_mul(D, Diag), Dinv) == Diag
print("   purely diagonal Zorn matrices are fixed by the flow ✓")

print("§3  Upper/lower nilpotent null states")
Upper = (0, u, [0,0,0], 0)
Lower = (0, [0,0,0], v, 0)
Zero = (0, [0,0,0], [0,0,0], 0)
assert zorn_mul(Upper, Upper) == Zero
assert zorn_mul(Lower, Lower) == Zero
print("   upper and lower pure off-diagonal states square to zero ✓")

print("§4  Repeller/attractor asymptotics")
assert sp.limit(sp.exp(2*k*eps), eps, sp.oo) == sp.oo
assert sp.limit(sp.exp(-2*k*eps), eps, sp.oo) == 0
print("   for k>0: upper sector repels, lower sector contracts to zero ✓")

print()
print("zorn_scaling_flow.py: All identities verified")
