# Exact-rational Sage witnesses for Smith's retrocirculant Moore--Penrose inverse.

R.<a,b> = PolynomialRing(QQ)
F = FractionField(R)

def retro(x, y):
    return matrix(F, [[0, y], [x, 0]])

A = retro(a, b)
Ap = matrix(F, [[0, 1/a], [1/b, 0]])
assert A * Ap * A == A
assert Ap * A * Ap == Ap
assert (A * Ap).transpose() == A * Ap
assert (Ap * A).transpose() == Ap * A

A0 = matrix(QQ, [[0,3],[2,0]])
Ap0 = matrix(QQ, [[0,1/2],[1/3,0]])
assert A0 * Ap0 * A0 == A0
B0 = matrix(QQ, [[0,7],[5,0]])
prod = A0 * B0
assert prod[0,1] == 0 and prod[1,0] == 0
print("smith retrocirculant Moore-Penrose Sage certificate: ok")
