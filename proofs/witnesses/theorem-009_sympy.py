import sympy as sp

# Affine A1^(1) generalized Cartan matrix
A = sp.Matrix([[2, -2], [-2, 2]])
detA = A.det()

print("Affine A1^(1) Cartan matrix:")
sp.pprint(A)
print(f"\nDeterminant = {detA}")
print("det = 0 confirms this is an affine (untwisted) Kac-Moody algebra.")
print("The null eigenvector (delta) satisfies A * delta = 0.")

# Compute nullspace (imaginary root delta)
null = A.nullspace()
print(f"\nNullspace basis vectors: {null}")
delta = sp.Matrix([1, 1])
print(f"\nCanonical imaginary root delta = (1,1)^T")
print(f"A * delta = {A * delta}")
print("Thus delta is the primitive imaginary root of A1^(1).")
