
import sympy as sp
from sympy import symbols, simplify

# Defining basis vectors for conformal model
# Let's say we have e1, e2, ..., en for Euclidean space
# and e, e_bar for the extra dimensions
# e**2 = 1, e_bar**2 = -1
# We will just write out the formulas symbolically

x, n, n_bar, e, e_bar = symbols('x n n_bar e e_bar', commutative=False)
lambda_var = symbols('lambda')

# Null vectors n and n_bar
n_def = e + e_bar
n_bar_def = e - e_bar

def F(x):
    # F(x) = 1/2 * (x^2 n + 2x - n_bar)
    return 0.5 * (x**2 * n_def + 2*x - n_bar_def)

# We can encode more equations later
print("Sympy definitions created.")
