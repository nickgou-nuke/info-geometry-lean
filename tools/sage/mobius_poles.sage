from sage.all import *

var('a b c d z')

# Symbolically compute z_infty and Z_infty
z_infty = -d/c
Z_infty = a/c

print(f"z_infty = {z_infty}")
print(f"Z_infty = {Z_infty}")

# Fixed points from cz^2 + (d-a)z - b = 0
# Quadratic formula: z = ( -(d-a) +/- sqrt((d-a)^2 - 4*c*(-b)) ) / 2c
# = (a-d +/- sqrt((d-a)^2 + 4bc)) / 2c
Delta = (d-a)^2 + 4*b*c
gamma_1 = ((a-d) + sqrt(Delta)) / (2*c)
gamma_2 = ((a-d) - sqrt(Delta)) / (2*c)

print(f"gamma_1 = {gamma_1}")
print(f"gamma_2 = {gamma_2}")

# Verify characteristic parallelogram equation: gamma_1 + gamma_2 = z_infty + Z_infty
sum_gamma = (gamma_1 + gamma_2).simplify_full()
sum_poles = (z_infty + Z_infty).simplify_full()

is_parallelogram_eq_valid = bool((sum_gamma - sum_poles).simplify_full() == 0)
print(f"Characteristic parallelogram equation gamma_1 + gamma_2 == z_infty + Z_infty identically: {is_parallelogram_eq_valid}")

# Matrix H
H = Matrix([[a, b], [c, d]])

# Calculate eigenvalues
eigenvalues = H.eigenvalues()
print(f"Eigenvalues of H from SageMath: {eigenvalues}")

# Verify lambda_i = c*gamma_i + d
lambda_1 = c*gamma_1 + d
lambda_2 = c*gamma_2 + d

print(f"lambda_1 (c*gamma_1 + d) = {lambda_1}")
print(f"lambda_2 (c*gamma_2 + d) = {lambda_2}")

# Check if lambda_1 and lambda_2 are indeed roots of the characteristic polynomial
charpoly = H.charpoly('x')
is_lambda_1_eigenvalue = bool(charpoly(x=lambda_1).simplify_full() == 0)
is_lambda_2_eigenvalue = bool(charpoly(x=lambda_2).simplify_full() == 0)

print(f"lambda_1 is an eigenvalue: {is_lambda_1_eigenvalue}")
print(f"lambda_2 is an eigenvalue: {is_lambda_2_eigenvalue}")

# Characteristic constant k = lambda_1 / lambda_2
k = lambda_1 / lambda_2
print(f"Characteristic constant k = lambda_1 / lambda_2 = {k}")
