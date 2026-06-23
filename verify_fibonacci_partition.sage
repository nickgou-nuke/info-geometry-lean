# SageMath verification of Fibonacci partition and supersymmetry

# 1. Golden ratios
Phi = (1 + sqrt(5)) / 2
phi = (sqrt(5) - 1) / 2

# Verify properties
assert Phi == 1 + phi
assert Phi^2 == Phi + 1
assert 20 * Phi^4 == 100 + 60 * phi
print("SageMath: Golden ratio and Fibonacci scale decomposition verified.")

# 2. SUSY partition difference
x = var('x')
B = 1 / (1 - x)
F = 1 + x
assert (B - F).simplify_full() == (x^2 / (1 - x)).simplify_full()
print("SageMath: SUSY partition difference identity verified.")

# 3. Numerical evaluation
scale = 20 * Phi^4
beta = float(scale.n())
print(f"SageMath: beta = {beta}")
p = 2
x_val = p^(-beta)
diff = x_val^2 / (1 - x_val)
print(f"SageMath: SUSY difference for p=2 is {diff}")
assert diff < 1e-80
print("SageMath: Supersymmetry checks completed successfully.")
