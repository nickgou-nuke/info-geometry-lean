# SageMath code: compute the dimension of QQ[x,y]/(x*(x-1), y) using normal basis.
R.<x,y> = QQ[]
I = ideal(x*(x-1), y)
nb = I.normal_basis()
print("Normal basis (monomials) of QQ[x,y]/I:", nb)
dim = len(nb)
print("Vector space dimension over QQ:", dim)
# Verify that the dimension is 2.
assert dim == 2, f"Expected dimension 2, got {dim}"
print("Success: dimension is 2.")