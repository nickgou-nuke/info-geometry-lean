# tools/sage/mobius_geometry.sage
var('a b c d z')

print("1. Original Mobius transformation:")
f = (a*z + b)/(c*z + d)
print(f"f(z) = {f}")

print("\n2. Four simple generators:")
T1 = z + d/c
I = 1/z
M = (b*c - a*d)/(c^2) * z
T2 = z + a/c

print(f"T1(z) = {T1}")
print(f"I(z) = {I}")
print(f"M(z) = {M}")
print(f"T2(z) = {T2}")

print("\n3. Verifying composition T2(M(I(T1(z)))) == f(z):")
comp = T2.subs(z=M.subs(z=I.subs(z=T1)))
print(f"Composition: {comp}")
diff = comp - f
diff_sim = diff.simplify_full()
print(f"Difference simplified: {diff_sim}")
assert diff_sim == 0, "Composition does not match original!"

print("\n4. Computing fixed points:")
# z = (a*z + b)/(c*z + d) => c*z^2 + (d-a)*z - b = 0
eq = c*z^2 + (d-a)*z - b == 0
sols = solve(eq, z)
print("Fixed points:")
for sol in sols:
    print(sol)

print("\n5. Verifying discriminant:")
# The roots of Az^2 + Bz + C = 0 have discriminant B^2 - 4AC
# Here A = c, B = (d-a), C = -b
disc_computed = (d-a)^2 - 4*c*(-b)
disc_expected = (a+d)^2 - 4*(a*d - b*c)
disc_diff = (disc_computed - disc_expected).simplify_full()
print(f"Computed discriminant: {disc_computed}")
print(f"Expected discriminant: {disc_expected}")
print(f"Discriminants match: {disc_diff == 0}")
assert disc_diff == 0, "Discriminants do not match!"

print("\nSuccess: All Mobius geometry properties verified.")
