# Wareham CGA formalization in SageMath
# We use a symbolic geometric algebra

e1, e2, e3, e_conformal, e_bar = var('e1 e2 e3 e_conformal e_bar')

# Null vectors n and n_bar
n = e_conformal + e_bar
n_bar = e_conformal - e_bar

# F(x) = 1/2(x^2 n + 2x - n_bar)
def F(x_sq, x_vec):
    return 0.5 * (x_sq * n + 2 * x_vec - n_bar)

# Dual of a circle C* = B - 1/2 rho^2 n
def circle_dual(B, rho):
    return B - 0.5 * rho**2 * n

print("SageMath CGA definitions loaded.")
