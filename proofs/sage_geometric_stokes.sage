# Exact Sage witness for the planar geometric Stokes boundary residue.
# Run with: sage proofs/sage_geometric_stokes.sage

var('t x y')
Ax = -y / (x^2 + y^2)
Ay = x / (x^2 + y^2)

curl_coeff = diff(Ay, x) - diff(Ax, y)
assert bool(curl_coeff.simplify_full() == 0)

integrand = (Ax.subs({x: cos(t), y: sin(t)}) * diff(cos(t), t)
             + Ay.subs({x: cos(t), y: sin(t)}) * diff(sin(t), t)).simplify_full()
assert bool(integrand == 1)

boundary_integral = integrate(integrand, t, 0, 2*pi)
assert bool((boundary_integral - 2*pi).simplify_full() == 0)

# Formal bivector symbol J with J^2 = -1, represented by the quotient QQ[J]/(J^2+1).
R.<J> = PolynomialRing(QQ)
Q = R.quotient(J^2 + 1, 'j')
j = Q.gen()
assert j^2 == -1

print("sage_curl_coeff_off_origin =", curl_coeff.simplify_full())
print("sage_unit_circle_integrand =", integrand)
print("sage_boundary_integral =", boundary_integral)
print("sage_J_square =", j^2)
print("sage geometric Stokes certificate: ok")
