print("Initializing symbolic variables...")
var('z k gamma_1 gamma_2 beta gamma')

print("\n--- Non-Parabolic Case ---")
a_np = (gamma_1 - k * gamma_2) / (gamma_1 - gamma_2)
b_np = gamma_1 * gamma_2 * (k - 1) / (gamma_1 - gamma_2)
c_np = (1 - k) / (gamma_1 - gamma_2)
d_np = (k * gamma_1 - gamma_2) / (gamma_1 - gamma_2)

H_np = matrix([[a_np, b_np], [c_np, d_np]])
print("Matrix H_np (k; gamma_1, gamma_2):")
print(H_np)

det_np = H_np.det().simplify_full()
print("Determinant of H_np:", det_np)
assert det_np == k, f"Determinant of non-parabolic matrix is {det_np}, expected {k}!"

f_np = (a_np * z + b_np) / (c_np * z + d_np)

LHS_np = (f_np - gamma_1) / (f_np - gamma_2)
RHS_np = k * (z - gamma_1) / (z - gamma_2)

diff_np = (LHS_np - RHS_np).simplify_full()
print("Difference (LHS - RHS) for non-parabolic equation:", diff_np)
assert diff_np == 0, "Non-parabolic fixed point equation not satisfied!"

print("\n--- Parabolic Case ---")
a_p = 1 + beta * gamma
b_p = -beta * gamma^2
c_p = beta
d_p = 1 - beta * gamma

H_p = matrix([[a_p, b_p], [c_p, d_p]])
print("Matrix H_p (beta; gamma):")
print(H_p)

det_p = H_p.det().simplify_full()
print("Determinant of H_p:", det_p)
assert det_p == 1, f"Determinant of parabolic matrix is {det_p}, expected 1!"

f_p = (a_p * z + b_p) / (c_p * z + d_p)

LHS_p = 1 / (f_p - gamma)
RHS_p = 1 / (z - gamma) + beta

diff_p = (LHS_p - RHS_p).simplify_full()
print("Difference (LHS - RHS) for parabolic equation:", diff_p)
assert diff_p == 0, "Parabolic fixed point equation not satisfied!"

print("\nAll tests passed successfully!")
