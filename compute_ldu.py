import sympy as sp

edges = [(0, 1), (0, 2), (2, 3), (0, 4), (4, 5), (5, 6), (6, 7), (7, 8), (8, 9)]
A = sp.zeros(10, 10)
for i in range(10):
    A[i, i] = 2
for u, v in edges:
    A[u, v] = -1
    A[v, u] = -1

# We want P^T A P = D, where D is diagonal. 
# Equivalently, A = L D L^T. So P = (L^T)^{-1}.
L, D = A.LDLdecomposition()
P = (L.T).inv()
P_inv = L.T

print("D diagonal:")
print([D[i,i] for i in range(10)])

print("P matrix:")
print(sp.simplify(P))
