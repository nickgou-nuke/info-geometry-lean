import sys
try:
    from sympy import symbols, sin, cos, Function
    from galgebra.ga import Ga
    from galgebra.printer import Format
except ImportError:
    print("SymPy or GAlgebra not installed. Please install them first.")
    sys.exit(1)

# Removed Format() to ensure console output works properly

# Define spacetime coordinates
coords = symbols('t x y z', real=True)

# Define 4D spacetime algebra (Minkowski metric +---)
sp3d = Ga('e*t|x|y|z', g=[1, -1, -1, -1], coords=coords)
t, x, y, z = sp3d.coords

# Geometric derivative (Dirac operator D = d + \\delta)
grad = sp3d.grad

# Define a vector field A (metriplectic vector field)
A = sp3d.mv('A', 'vector', f=True)

print("=== Metriplectic Vector Field A ===")
print(A)

# The Chiral Dirac-Hodge operator is the geometric derivative
D_A = grad * A

print("\n=== Dirac-Hodge Operator D acting on A (grad * A) ===")
print(D_A)

# Decomposition into exact (curl) and co-exact (divergence) forms
div_A = grad | A # Inner product (co-exact, divergence, \\delta)
curl_A = grad ^ A # Outer product (exact, curl, d)

print("\n=== Co-exact part (divergence / \\delta A) ===")
print(div_A)

print("\n=== Exact part (exterior derivative / d A) ===")
print(curl_A)
