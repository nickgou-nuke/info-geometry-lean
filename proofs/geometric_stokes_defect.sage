# Sage exact-rational/trigonometric certificate for the unit-circle defect angle.
var('t')
x = cos(t); y = sin(t)
dx = diff(x, t); dy = diff(y, t)
r2 = x**2 + y**2
integrand = simplify((-y/r2)*dx + (x/r2)*dy)
assert bool(integrand == 1)
angle = integral(integrand, t, 0, 2*pi)
assert bool(angle == 2*pi)
print('geometric_stokes_defect.sage: exact angle 2*pi check passed')
