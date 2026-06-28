# tools/sympy/tkk_d4.py
import sympy as sp
from sympy import Matrix

print("SymPy test for TKK framework")
# Define symbols
x, y = sp.symbols('x y')
expr = x**2 - y**2
print("Expression:", expr)
print("Factorized:", sp.factor(expr))

# Simple matrix
M = sp.Matrix([[1,2],[3,4]])
print("Matrix M:", M)
print("Determinant:", M.det())

# Example of constructing Cartan-like matrices for D4 (just a placeholder)
# Cartan matrix of D4
Cartan = Matrix([[ 2, -1,  0,  0],
                 [-1,  2, -1, -1],
                 [ 0, -1,  2,  0],
                 [ 0, -1,  0,  2]])
print("Cartan matrix of D4:")
sp.pprint(Cartan)
print("Success.")