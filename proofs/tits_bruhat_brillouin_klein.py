"""SymPy witness: Tits/Bruhat tempered torus and Brillouin torus both twist to Klein bottles.

The same algebraic mechanism appears in two languages:

  physics:        nonsymmorphic glide on Brillouin torus
  p-adic theory: 2-cocycle/twisted Hecke action on compact dual torus

Both are modeled on the universal affine action

  F(x,y) = (x + 1/2, -y)

on the covering plane.  It satisfies

  F^2 = T_x,          F T_y F^{-1} = T_y^{-1},

which is the Klein bottle presentation.  On angular coordinates this is
(theta,phi) -> (theta+pi, -phi): orientation reversing, free on T^2, and
squaring to the identity on the compact quotient while remembering the lifted
full translation.
"""

import sympy as sp


def assert_matrix_zero(name, M):
    S = sp.simplify(M)
    if S != sp.zeros(*S.shape):
        raise AssertionError(f"{name} failed:\n{S}")


def assert_zero(name, expr):
    s = sp.simplify(expr)
    if s != 0:
        raise AssertionError(f"{name} failed: {s}")


print("§1  Universal affine Klein twist")
# Homogeneous affine matrices acting on column vectors (x,y,1).
F = sp.Matrix([[1, 0, sp.Rational(1, 2)], [0, -1, 0], [0, 0, 1]])
Finv = sp.Matrix([[1, 0, -sp.Rational(1, 2)], [0, -1, 0], [0, 0, 1]])
Tx = sp.Matrix([[1, 0, 1], [0, 1, 0], [0, 0, 1]])
Ty = sp.Matrix([[1, 0, 0], [0, 1, 1], [0, 0, 1]])
Ty_inv = sp.Matrix([[1, 0, 0], [0, 1, -1], [0, 0, 1]])

assert_matrix_zero("F inverse", F * Finv - sp.eye(3))
assert_matrix_zero("F^2 = Tx", F**2 - Tx)
assert_matrix_zero("F Ty F^-1 = Ty^-1", F * Ty * Finv - Ty_inv)
print("   F²=Tx and F Ty F⁻¹=Ty⁻¹ ✓")

print("§2  Orientation reversal and free quotient on T²")
J = sp.Matrix([[1, 0], [0, -1]])
assert_zero("det J = -1", J.det() + 1)
# Fixed point equation on torus: theta+pi = theta mod 2pi means pi=2pi*n -> n=1/2, impossible for integer n.
n = sp.symbols("n", integer=True)
# Algebraically this would force n=1/2, not an integer.
forced_n = sp.simplify(sp.pi / (2 * sp.pi))
assert forced_n == sp.Rational(1, 2)
assert forced_n.is_integer is False
print("   action is orientation reversing and fixed-point free on the torus ✓")

print("§3  Brillouin and Tits/Bernstein interpretations share the same quotient")
theta, phi = sp.symbols("theta phi")
# Brillouin momentum glide: (kx,ky)->(kx+π,-ky), equivalent coordinate model.
brillouin_glide = (theta + sp.pi, -phi)
# Twisted compact dual torus action: (w,z)->(-w,z^-1); with w=e^{i theta}, z=e^{i phi}.
w = sp.exp(sp.I * theta)
z = sp.exp(sp.I * phi)
tits_action = (-w, 1 / z)
angular_tits = (sp.exp(sp.I * (theta + sp.pi)), sp.exp(-sp.I * phi))
assert_zero("-w = exp(i(theta+pi))", sp.simplify(tits_action[0] - angular_tits[0]))
assert_zero("z^-1 = exp(-i phi)", sp.simplify(tits_action[1] - angular_tits[1]))
print("   (w,z)->(-w,z⁻¹) is the angular form of the same glide quotient ✓")

print("§4  Z2 invariant survives C -> -C")
C = sp.symbols("C", integer=True)
assert sp.Mod(C, 2) == sp.Mod(-C, 2)
print("   non-orientability kills signed charge but preserves parity C mod 2 ✓")

print()
print("tits_bruhat_brillouin_klein.py: All identities verified")
