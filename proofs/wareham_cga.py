import sympy as sp
from sympy import symbols, simplify

# Wareham CGA formalization in Sympy
# Basis: e1, e2, e, e_bar
# n = e + e_bar, n_bar = e - e_bar

x, y, a, b, l, rho = symbols('x y a b l rho', real=True)
e1, e2, e, e_bar = symbols('e1 e2 e e_bar', commutative=False)

n = e + e_bar
n_bar = e - e_bar

# Null vector representation of a point
def F(vec_sq, vec):
    # F(x) = 1/2(x^2 n + 2x - n_bar)
    return 0.5 * (vec_sq * n + 2*vec - n_bar)

# Incidence relation of a plane
# X ^ X1 ^ X2 ^ X3 ^ X4 = 0
# Dual of a plane Phi* = d n + e3
def plane_dual(d, n_hat):
    return d * n + n_hat

# Dual of a circle C* = B - 1/2 rho^2 n
def circle_dual(B, rho):
    return B - 0.5 * rho**2 * n

print("Sympy CGA definitions initialized.")
