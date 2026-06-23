# Exact-rational Sage witnesses for Rose's Drazin-inverse computation.

R.<x> = PolynomialRing(QQ)
f1 = x^2 + 5*x + 1
p1 = -24*x - 115
assert (x^3 * p1 - 1) % f1 == 0

C1 = matrix(QQ, [[0, -1], [1, -5]])
A1 = block_diagonal_matrix(matrix(QQ, 2, 2, 0), C1)
D1 = A1^2 * (-24*A1 - 115*identity_matrix(QQ, 4))
assert A1^3 * D1 == A1^2
assert D1 * A1 == A1 * D1
assert C1.charpoly(x) == f1

f2 = x^4 + x^3 + x^2 + x + 1
assert (x * x^4 - 1) % f2 == 0
print("rose Drazin computation Sage certificate: ok")
