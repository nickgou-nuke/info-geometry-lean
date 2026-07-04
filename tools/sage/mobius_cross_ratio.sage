print("Starting symbolic algebraic verification of Möbius properties...")

# Declare ring and variables
var('z1 z2 z3 z4 a b c d z')

# Define the Möbius transformation
f(z) = (a*z + b)/(c*z + d)

# 1. Cross-Ratio invariance
cr_original = (z1 - z3)*(z2 - z4) / ((z1 - z4)*(z2 - z3))
cr_transformed = (f(z1) - f(z3))*(f(z2) - f(z4)) / ((f(z1) - f(z4))*(f(z2) - f(z3)))

print("Checking Cross-Ratio invariance...")
diff = (cr_original - cr_transformed).simplify_full()
print("Difference after simplification: {}".format(diff))
if diff == 0:
    print("Cross-Ratio invariance verified: TRUE")
else:
    print("Cross-Ratio invariance verified: FALSE")

# 2. Fixed-point roots and discriminant
print("\nComputing fixed-point roots for f(z) = z...")
eq = c*z^2 + (d - a)*z - b == 0
roots = solve(eq, z)
print("Fixed-point roots: {}".format(roots))

print("\nEvaluating discriminant of the fixed-point quadratic equation...")
Delta_quadratic = (d - a)^2 - 4*c*(-b)
Delta_requested = (a + d)^2 - 4*(a*d - b*c)

print("Quadratic Discriminant: {}".format(Delta_quadratic))
print("Requested Discriminant form: {}".format(Delta_requested))
diff_delta = (Delta_quadratic - Delta_requested).simplify_full()
if diff_delta == 0:
    print("The discriminant matches the formula Delta = (a+d)^2 - 4(ad-bc).")

print("Done.")
