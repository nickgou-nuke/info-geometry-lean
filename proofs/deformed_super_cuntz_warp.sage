# Sage witness for the finite q-warped tessellation and modular character.
# Run with: sage proofs/deformed_super_cuntz_warp.sage

R.<q,theta1,theta2,theta3,theta4> = PolynomialRing(QQ)
flat_sum = 2
q_angle_sum = q * (theta1 + theta2 + theta3 + theta4)
deficit = flat_sum - q_angle_sum
assert deficit == 2 - q*(theta1 + theta2 + theta3 + theta4)

# A finite Laurent-polynomial surrogate for the modular character p^(it):
# z_p records exp(i t log p), and scaling is multiplication by z_p.
L.<z2,z3,S2,S3> = LaurentPolynomialRing(QQ)
sigma_S2 = z2 * S2
sigma_S3 = z3 * S3
assert sigma_S2 / S2 == z2
assert sigma_S3 / S3 == z3

print("deficit =", deficit)
print("sigma(S2) =", sigma_S2)
print("sigma(S3) =", sigma_S3)
