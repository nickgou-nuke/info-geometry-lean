var('a alpha theta lambda_')

print("--- Parabolic ---")
H_parabolic = matrix([[1, a], [0, 1]])
sigma_parabolic = H_parabolic.trace()^2
expected_parabolic = 4
print(f"Matrix:\n{H_parabolic}")
print(f"Computed sigma: {sigma_parabolic}")
print(f"Expected sigma: {expected_parabolic}")
print(f"Matches: {bool(sigma_parabolic == expected_parabolic)}\n")

print("--- Elliptic ---")
H_elliptic = matrix([[cos(alpha), -sin(alpha)], [sin(alpha), cos(alpha)]])
sigma_elliptic = (H_elliptic.trace()^2).simplify_trig()
expected_elliptic = 4*cos(alpha)^2
print(f"Matrix:\n{H_elliptic}")
print(f"Computed sigma: {sigma_elliptic}")
print(f"Expected sigma: {expected_elliptic}")
print(f"Matches: {bool((sigma_elliptic - expected_elliptic).simplify_trig() == 0)}\n")

print("--- Hyperbolic ---")
H_hyperbolic = matrix([[exp(theta/2), 0], [0, exp(-theta/2)]])
sigma_hyperbolic = H_hyperbolic.trace()^2
expected_hyperbolic = 4*cosh(theta/2)^2
print(f"Matrix:\n{H_hyperbolic}")
print(f"Computed sigma: {sigma_hyperbolic}")
print(f"Expected sigma: {expected_hyperbolic}")
diff_hyperbolic = (sigma_hyperbolic - expected_hyperbolic.exponentialize()).simplify_full()
print(f"Matches: {bool(diff_hyperbolic == 0)}\n")

print("--- Loxodromic ---")
H_loxodromic = matrix([[lambda_, 0], [0, 1/lambda_]])
sigma_loxodromic = H_loxodromic.trace()^2
expected_loxodromic = (lambda_ + 1/lambda_)^2
print(f"Matrix:\n{H_loxodromic}")
print(f"Computed sigma: {sigma_loxodromic}")
print(f"Expected sigma: {expected_loxodromic}")
diff_loxodromic = (sigma_loxodromic - expected_loxodromic).simplify_full()
print(f"Matches: {bool(diff_loxodromic == 0)}\n")
