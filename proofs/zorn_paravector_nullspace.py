"""SymPy witness: Zorn paravector mass shell and nullspace collapse.

A relativistic four-momentum is encoded as the split-octonion/Zorn paravector

    P = [[E, p], [p, E]]

with norm N(P)=ab-u·v = E^2-|p|^2.  The RG/nullspace collapse removes the
scalar/associative energy and leaves the lower nilpotent

    Z = [[0, 0], [p, 0]],

which has N(Z)=0 and Z^2=0.  This is the algebraic lightcone/parafermion socket.
"""

import sympy as sp


def dot(x, y):
    return sum(xi * yi for xi, yi in zip(x, y))


def cross(x, y):
    return [
        x[1] * y[2] - x[2] * y[1],
        x[2] * y[0] - x[0] * y[2],
        x[0] * y[1] - x[1] * y[0],
    ]


def zorn_mul(X, Y):
    # tuple order: (a,b,u,v) = [[a,u],[v,b]]
    a, b, u, v = X
    c, d, w, z = Y
    return (
        sp.simplify(a*c + dot(u, z)),
        sp.simplify(b*d + dot(v, w)),
        [sp.simplify(a*w[i] + d*u[i] - cross(v, z)[i]) for i in range(3)],
        [sp.simplify(c*v[i] + b*z[i] + cross(u, w)[i]) for i in range(3)],
    )


def zorn_norm(X):
    a, b, u, v = X
    return sp.simplify(a*b - dot(u, v))


print("§1  Zorn paravector mass shell")
E, px, py, pz, m = sp.symbols("E px py pz m", real=True)
p = [px, py, pz]
P = (E, E, p, p)
N_P = zorn_norm(P)
assert sp.expand(N_P) == E**2 - px**2 - py**2 - pz**2
assert sp.simplify(sp.Eq(N_P, m**2).lhs - (E**2 - dot(p, p))) == 0
print("   N(P)=E²-|p|², the mass-shell quadratic ✓")

print("§2  Collapsed lower nullspace defect")
Z = (0, 0, [0, 0, 0], p)
Zero = (0, 0, [0, 0, 0], [0, 0, 0])
assert zorn_norm(Z) == 0
assert zorn_mul(Z, Z) == Zero
print("   collapsed Z has N(Z)=0 and Z²=0 ✓")

print("§3  Lightcone/massless condition")
lightcone = sp.Eq(E**2 - dot(p, p), 0)
assert sp.solve(lightcone, E) == [-sp.sqrt(px**2 + py**2 + pz**2), sp.sqrt(px**2 + py**2 + pz**2)]
print("   massless shell is E=±|p|; collapsed state is strictly null ✓")

print()
print("zorn_paravector_nullspace.py: All identities verified")
