# Exact-rational Sage certificate for the planar geometric Stokes residue and
# the associated spinorial parity flip.
#
# This is a finite symbolic witness only.  The Lean theorem is the owner of the
# algebraic monodromy readout; this script certifies the same residue data in
# Sage's exact symbolic lane.

x, y, t = var('x y t', domain='real')

Ax = -y / (x**2 + y**2)
Ay = x / (x**2 + y**2)

gamma = {x: cos(t), y: sin(t)}
integrand = (Ax.subs(gamma) * diff(cos(t), t) + Ay.subs(gamma) * diff(sin(t), t)).simplify_full()
assert integrand == 1

boundary_integral = integrate(integrand, t, 0, 2*pi)
assert boundary_integral == 2*pi

J = matrix(QQ, [[0, -1], [1, 0]])
assert J**2 == -identity_matrix(QQ, 2)

spinor_scalar = cos(pi)
spinor_bivector_coeff = sin(pi)
assert spinor_scalar == -1
assert spinor_bivector_coeff == 0

print("A =", Ax, "* e_x +", Ay, "* e_y")
print("boundary_integral =", boundary_integral)
print("J^2 =", J**2)
print("spinor_transport_2pi = -1")
print("geometric stokes Sage certificate: ok")
