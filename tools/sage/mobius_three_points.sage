var('z z1 z2 z3')

a = z2 - z3
b = -z1 * (z2 - z3)
c = z2 - z1
d = -z3 * (z2 - z1)

f(z) = (a*z + b) / (c*z + d)

print("Testing z = z1:")
val_z1 = f(z1).simplify_full()
print("f(z1) =", val_z1)
assert val_z1 == 0, "f(z1) should be 0"

print("\nTesting z = z2:")
val_z2 = f(z2).simplify_full()
print("f(z2) =", val_z2)
assert val_z2 == 1, "f(z2) should be 1"

print("\nTesting z -> z3:")
num = a*z + b
den = c*z + d

val_num_z3 = num(z=z3).simplify_full()
val_den_z3 = den(z=z3).simplify_full()

print("Numerator at z3 =", val_num_z3.factor())
print("Denominator at z3 =", val_den_z3)
assert val_den_z3 == 0, "Denominator should be 0 at z3"
# The numerator at z3 factors to -(z1 - z3)*(z2 - z3)
# As long as points are distinct, the numerator is non-zero,
# so the fractional linear transformation evaluates to infinity.
print("Since denominator is 0 and numerator is non-zero (for distinct points), f(z3) evaluates to infinity.")

print("\nAll checks passed!")
