"""SymPy witness: log-det self-concordant barrier and Super-Kähler deferred_interface.

For the positive biquaternion/Hermitian cone, the canonical barrier is
    f(X) = -log det(X).
On a diagonal chart X=diag(x,y): f=-log(xy).  The Hessian is diag(1/x^2,1/y^2).
The scalar barrier f(x)=-log x saturates the self-concordance identity
    (f'''(x))^2 = 4 (f''(x))^3.
"""

import sympy as sp

print("§1  log-det barrier on diagonal biquaternion cone")
x, y = sp.symbols("x y", positive=True)
X = sp.diag(x, y)
f = -sp.log(X.det())
assert f == -sp.log(x*y)
H = sp.hessian(f, (x, y))
assert sp.simplify(H - sp.diag(1/x**2, 1/y**2)) == sp.zeros(2)
print("   f=-log det(X), Hessian=diag(1/x²,1/y²) ✓")

print("§2  scalar self-concordance saturation")
t = sp.symbols("t", positive=True)
fs = -sp.log(t)
f2 = sp.diff(fs, t, 2)
f3 = sp.diff(fs, t, 3)
assert f2 == t**-2
assert f3 == -2*t**-3
assert sp.simplify(f3**2 - 4*f2**3) == 0
print("   (-log x) satisfies (f''')²=4(f'')³ ✓")

print("§3  boundary divergence and nilpotent sink")
eps = sp.symbols("eps", positive=True)
barrier_eps = -sp.log(eps*y)
assert sp.limit(barrier_eps, eps, 0, dir='+') == sp.oo
Z = sp.Matrix([[0, 1], [0, 0]])
assert Z**2 == sp.zeros(2)
print("   det→0 barrier diverges; square-zero nilpotent marks boundary sink ✓")

print()
print("logdet_superkahler_barrier.py: All identities verified")
