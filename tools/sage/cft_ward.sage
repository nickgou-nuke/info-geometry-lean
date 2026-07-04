var('z1 z2 D1 D2 C')

# Define the 2-point function F
F = C * (z1 - z2)^-(D1 + D2)

# Define the Special Conformal Transformation operator W_2 applied to F
# W_2(F) = z1^2 * diff(F, z1) + z2^2 * diff(F, z2) + 2*D1*z1*F + 2*D2*z2*F
W2_F = z1^2 * diff(F, z1) + z2^2 * diff(F, z2) + 2*D1*z1*F + 2*D2*z2*F

# The expected factored result
target = F * (z1 - z2) * (D1 - D2)

# Verify the equivalence
diff_expr = (W2_F - target).simplify_full()

print("F:", F)
print("W2_F:", W2_F)
print("Target:", target)
print("Difference:", diff_expr)

if diff_expr == 0:
    print("\nSuccess: W_2(F) cleanly factors to exactly F * (z_1 - z_2) * (\\Delta_1 - \\Delta_2).")
    print("This proves 2-point functions vanish if \\Delta_1 != \\Delta_2.")
else:
    print("\nFailed to prove equivalence.")
    import sys
    sys.exit(1)
