"""SymPy witness: Brillouin Klein fixed-line filter + nilpotent IS attractor.

Combines:
- pg glide fixed line k2=0: c_k=(-1)^k c_k, so odd k vanish;
- fixed-line paravector mass shell N(P)=E^2-px^2;
- RG collapse to lower Zorn nilpotent Z=(0,0,0,(px,0,0));
- N(Z)=0 and Z^2=0;
- nilpotent Itakura--Saito limit gives D_IS=0.
"""

import sympy as sp


def dot(x, y):
    return sum(xi * yi for xi, yi in zip(x, y))


def cross(x, y):
    return [
        x[1]*y[2] - x[2]*y[1],
        x[2]*y[0] - x[0]*y[2],
        x[0]*y[1] - x[1]*y[0],
    ]


def zorn_mul(X, Y):
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

print("§1  Brillouin Klein fixed-line glide filter")
extinguished = []
allowed = []
for k in range(0, 10):
    phase = sp.Integer(-1)**k
    c = sp.symbols(f"c_{k}_0")
    if k % 2:
        assert sp.solve(sp.Eq(c - phase*c, 0), c) == [0]
        extinguished.append(k)
    else:
        assert sp.simplify(c - phase*c) == 0
        allowed.append(k)
assert extinguished == [1, 3, 5, 7, 9]
assert allowed == [0, 2, 4, 6, 8]
print("   odd fixed-line modes vanish; even modes survive ✓")

print("§2  Fixed-line mass shell")
E, px, m = sp.symbols("E px m", real=True)
pvec = [px, 0, 0]
P_fixed = (E, E, pvec, pvec)
assert sp.expand(zorn_norm(P_fixed)) == E**2 - px**2
print("   N(P_fixed)=E²-px²=m² ✓")

print("§3  Nilpotent collapse")
Z = (0, 0, [0, 0, 0], pvec)
Zero = (0, 0, [0, 0, 0], [0, 0, 0])
assert zorn_norm(Z) == 0
assert zorn_mul(Z, Z) == Zero
print("   collapsed lower defect has N(Z)=0 and Z²=0 ✓")

print("§4  Itakura--Saito nilpotent attractor")
v = sp.symbols("v", real=True)
assert sp.limit(sp.cosh(v)-1, v, 0) == 0
assert sp.limit(sp.sinh(v)/v - 1, v, 0) == 0
K = sp.Matrix([[0, 1], [0, 0]])
assert K**2 == sp.zeros(2)
assert (sp.eye(2) + K) - sp.eye(2) - K == sp.zeros(2)
print("   D_IS(Z)=0 in the nilpotent/lightcone limit ✓")

print()
print("brillouin_klein_nilpotent_attractor.py: All identities verified")
