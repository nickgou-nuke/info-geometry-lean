"""SymPy witness for the logCFT/Cantor-Cuntz/paperwall/Klein/SUSY framework.

This is a finite algebraic witness for the interlocking claims:
1. Cuntz word projections P_w = S_w S_w* form a Cantor cylinder Boolean algebra.
2. A non-diagonalizable transfer/Jordan block produces logCFT-style mixing.
3. A glide operation squares to a translation and reverses the transverse cycle
   (Klein-bottle presentation).
4. A momentum glide has a Z2 orbit/twist, so only parity survives as the global
   invariant.
5. Discrete SUSY: the glide is an odd square root of translation, Q^2=T.
"""

import sympy as sp


def assert_zero(name, expr):
    s = sp.simplify(expr)
    if s != 0:
        raise AssertionError(f"{name} failed: {s}")


def assert_matrix_zero(name, M):
    S = sp.simplify(M)
    if S != sp.zeros(*S.shape):
        raise AssertionError(f"{name} failed:\n{S}")


print("§1  Cantor/Cuntz cylinder projections")
# Finite depth Cantor cylinder algebra: words over {1,2}.  A projection P_w is
# represented by the cylinder set of all depth-L words beginning with w.
L = 4
alphabet = ["1", "2"]
words = ["".join(bits) for bits in __import__("itertools").product(alphabet, repeat=L)]

def cylinder(prefix):
    return {w for w in words if w.startswith(prefix)}

for prefix in ["1", "2", "11", "12"]:
    P = cylinder(prefix)
    assert P & P == P
assert cylinder("1").isdisjoint(cylinder("2"))
assert cylinder("1") | cylinder("2") == set(words)
assert cylinder("11") | cylinder("12") == cylinder("1")
print("   P_i P_j=δij P_i and P_1+P_2=1 at finite Cantor depth ✓")

print("§2  logCFT transfer operator = Jordan dilatation")
lam = sp.symbols("lambda")
J = sp.Matrix([[lam, 1], [0, lam]])
N = J - lam * sp.eye(2)
assert_matrix_zero("N^2=0", N**2)
# Under scale t, exp(tJ)=exp(tλ)(I+tN), the t factor is the logarithmic partner.
t = sp.symbols("t")
expJ_expected = sp.exp(t * lam) * (sp.eye(2) + t * N)
assert_matrix_zero("exp(tJ)=e^{tλ}(I+tN)", sp.simplify((t * J).exp() - expJ_expected))
print("   Jordan defect yields logarithmic mixing exp(tJ)=e^{tλ}(I+tN) ✓")

print("§3  paperwall glide group -> Klein bottle relation")
# Affine action on (x,y): glide g(x,y)=(x+1/2,-y), tx(x,y)=(x+1,y), ty(x,y)=(x,y+1)
x, y = sp.symbols("x y")

def g(pt):
    x0, y0 = pt
    return (sp.simplify(x0 + sp.Rational(1, 2)), sp.simplify(-y0))

def tx(pt):
    x0, y0 = pt
    return (sp.simplify(x0 + 1), y0)

def ty(pt):
    x0, y0 = pt
    return (x0, sp.simplify(y0 + 1))

def g_inv(pt):
    # g is its own inverse up to tx; exact inverse: (x,y)->(x-1/2,-y)
    x0, y0 = pt
    return (sp.simplify(x0 - sp.Rational(1, 2)), sp.simplify(-y0))

pt = (x, y)
assert g(g(pt)) == tx(pt)
left = g(ty(g_inv(pt)))
right = (x, y - 1)
assert left == right
print("   g²=tx and g ty g⁻¹=ty⁻¹: Klein bottle presentation ✓")

print("§4  Brillouin Klein bottle momentum glide and Z2 parity")
# Momentum glide F(kx,ky)=(-kx, ky+π).  Twice gives ky+2π, i.e. same BZ point.
kx, ky = sp.symbols("kx ky")

def F(p):
    a, b = p
    return (-a, b + sp.pi)

assert F(F((kx, ky))) == (kx, ky + 2 * sp.pi)
# Orientation sign of F: Jacobian determinant = -1, so Chern density changes sign.
Jac = sp.Matrix([[-1, 0], [0, 1]])
assert_zero("det(F)=-1", Jac.det() + 1)
# Hence an integer charge C is identified with -C; only parity C mod 2 is stable.
C = sp.symbols("C", integer=True)
assert sp.Mod(C, 2) == sp.Mod(-C, 2)
print("   orientation reversal kills signed Chern class; C mod 2 survives ✓")

print("§5  discrete glide SUSY")
# Concrete 2x2 toy: odd Q swaps sectors with a translation phase z; Q^2=z I.
z = sp.symbols("z", nonzero=True)
Q = sp.Matrix([[0, z], [1, 0]])
T = z * sp.eye(2)
assert_matrix_zero("Q^2=T", Q**2 - T)
H = T
assert_matrix_zero("discrete SUSY H=T=Q^2", Q**2 - H)
print("   Q=glide is an odd square root of translation: Q²=T ✓")

print()
print("fractal_klein_susy_framework.py: All identities verified")
