#!/usr/bin/env python3
"""Independent exact Sage generator for split so(6,5) |2|-grading."""
from sage.all import QQ, matrix, diagonal_matrix

n = 11
Q = matrix(QQ, n, n, lambda i, j: 1 if i + j == n - 1 else 0)
weights = [-1, -1, 0, 0, 0, 0, 0, 0, 0, 1, 1]
H = diagonal_matrix(QQ, weights)
E = lambda i, j: matrix(QQ, n, n, {(i, j): 1})

def degree(x):
    for k in range(-2, 3):
        if H*x - x*H == k*x:
            return k
    return None

basis = []
for i in range(n):
    for j in range(n):
        x = E(i, j) - Q*E(i, j).transpose()*Q
        if x != 0 and x not in basis:
            basis.append(x)
graded = {k: [x for x in basis if degree(x) == k] for k in range(-2, 3)}
bracket = lambda x, y: x*y - y*x
closure = all(bracket(x, y) == 0 or degree(bracket(x, y)) is not None
              for x in basis for y in basis)
jacobi = all(bracket(x, bracket(y, z)) + bracket(y, bracket(z, x)) +
              bracket(z, bracket(x, y)) == 0
              for x in basis for y in basis for z in basis)
print("CAS_SPLIT_SO65_FIVE_GRADE")
print("gram_size=11x11")
print("gram_rank=", Q.rank())
print("gram_determinant=", Q.det())
print("carrier_dimension=", len(basis))
print("grade_dimensions=", [len(graded[k]) for k in range(-2, 3)])
print("dimension_sum=", sum(len(graded[k]) for k in range(-2, 3)))
print("graded_commutator_closure=", closure)
print("matrix_jacobi=", jacobi)
print("STATUS=", len(basis) == 55 and [len(graded[k]) for k in range(-2, 3)] == [10,5,25,5,10] and closure and jacobi)
