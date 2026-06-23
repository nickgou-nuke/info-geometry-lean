# Exact-rational Sage certificate for Campbell--Meyer weak Drazin inverses.

A = matrix(QQ, [[2,0,0],[0,0,1],[0,0,0]])
Bmin = matrix(QQ, [[QQ(1)/2,0,0],[0,0,0],[0,0,0]])
Bpoly = (QQ(1)/2) * identity_matrix(QQ, 3)
k = 2
assert Bmin * (A ** (k + 1)) == A ** k
assert Bpoly * (A ** (k + 1)) == A ** k
assert A * Bpoly == Bpoly * A
R.<x> = PolynomialRing(QQ)
char = A.charpoly(x)
assert char == x^2 * (x - 2)
print("weak Drazin Sage certificate: ok")
