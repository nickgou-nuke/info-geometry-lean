var('z, z0, theta, r')
assume(r > 0, 'real')
assume(theta, 'real')

# Line conjugation
def line_conjugate(z, z0, theta):
    return exp(2*I*theta) * conjugate(z - z0) + z0

# Circle conjugation
def circle_conjugate(z, z0, r):
    return r^2 / conjugate(z - z0) + z0

print("Testing circle conjugation is an involution:")
z_star = circle_conjugate(z, z0, r)
z_star_star = circle_conjugate(z_star, z0, r)
print("z_star =", z_star)
print("z_star_star =", z_star_star.simplify_full())

diff = (z_star_star - z).simplify_full()
print("z_star_star - z =", diff)
if diff == 0:
    print("Verification successful: it is an involution.")
else:
    raise AssertionError("Not an involution! Expected 0, got " + str(diff))

print("\nTesting points on the circle are fixed:")
# The equation for the circle is (z - z0) * conjugate(z - z0) == r^2
fixed_pt_expr = circle_conjugate(z, z0, r).subs(r^2 == (z - z0) * conjugate(z - z0))
print("z_star for point on circle:", fixed_pt_expr.simplify_full())
diff_on_circle = (fixed_pt_expr - z).simplify_full()
print("z_star - z for point on circle:", diff_on_circle)
if diff_on_circle == 0:
    print("Verification successful: points on the circle are fixed.")
else:
    raise AssertionError("Points on circle not fixed! Expected 0, got " + str(diff_on_circle))

print("Success!")
