"""SymPy witness for the Cuntz-deformed operator super-Poincare presentation.

This mirrors `CuntzDeformedSuperPoincare.lean` at the finite matrix level:
- odd--odd affine superbracket interpolates Lie and Jordan products;
- the operator-valued relation {Q,Qbar}=2P transports by L(-)R;
- an x-boost preserves the Minkowski mass Casimir.
"""
import sympy as sp

print("§1 Cuntz/BdG odd--odd affine bracket")
beta = sp.symbols("beta")
a, b, c, d, e, f, g, h = sp.symbols("a b c d e f g h")
X = sp.Matrix([[a, b], [c, d]])
Y = sp.Matrix([[e, f], [g, h]])
lie = X * Y - Y * X
jordan = X * Y + Y * X
affine = X * Y + (2 * beta - 1) * (Y * X)
assert sp.simplify(affine.subs(beta, 0) - lie) == sp.zeros(2)
assert sp.simplify(affine.subs(beta, 1) - jordan) == sp.zeros(2)
assert sp.simplify(affine - ((1 - beta) * lie + beta * jordan)) == sp.zeros(2)
print("   β=0 Lie, β=1 Jordan/anticommutator, affine split ✓")

print("§2 operator-valued super-Poincare relation and spin transport")
l11, l12, l21, l22, r11, r12, r21, r22 = sp.symbols("l11 l12 l21 l22 r11 r12 r21 r22")
p11, p12, p21, p22 = sp.symbols("p11 p12 p21 p22")
L = sp.Matrix([[l11, l12], [l21, l22]])
R = sp.Matrix([[r11, r12], [r21, r22]])
P = sp.Matrix([[p11, p12], [p21, p22]])
anti_QQbar = 2 * P  # operator matrix relation, not scalar central charge
transported_left = L * anti_QQbar * R
transported_right = 2 * (L * P * R)
assert sp.simplify(transported_left - transported_right) == sp.zeros(2)
print("   L {Q,Qbar} R = 2 L P R ✓")

print("§3 Lorentz x-boost mass Casimir")
phi, E, px, py, pz = sp.symbols("phi E px py pz")
ch = sp.cosh(phi)
sh = sp.sinh(phi)
Ep = ch * E + sh * px
pxp = sh * E + ch * px
mass_before = E**2 - px**2 - py**2 - pz**2
mass_after = sp.expand(Ep**2 - pxp**2 - py**2 - pz**2)
# SymPy does not always rewrite cosh^2-sinh^2 automatically; use the identity.
mass_after_reduced = sp.expand(mass_after.subs(sp.cosh(phi)**2, 1 + sp.sinh(phi)**2))
assert sp.simplify(mass_after_reduced - mass_before) == 0
print("   boost preserves E²-p² ✓")

print("cuntz_deformed_super_poincare.py: all identities verified")
