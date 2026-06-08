import sympy as sp
A = sp.Matrix(sp.symbols("a0:9")).reshape(3,3)
B = sp.Matrix(sp.symbols("b0:9")).reshape(3,3)
result = sp.simplify(sp.trace(A*B - B*A))
print(f"tr([A,B]) = {result}")
