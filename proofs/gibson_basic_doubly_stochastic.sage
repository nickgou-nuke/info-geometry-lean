# Exact-rational Sage witnesses for Gibson basic doubly stochastic matrices.

R.<x,b> = PolynomialRing(QQ)

def basic12(t):
    return matrix(R, [[t, 1 - t, 0], [1 - t, t, 0], [0, 0, 1]])

M = basic12(x)
ones = vector(R, [1, 1, 1])
assert M * ones == ones
assert M.transpose() * ones == ones
assert M.det() == 2*x - 1

A = basic12(R(QQ(2)/3))
B = basic12(R(QQ(3)/5))
P = A * B
assert P * ones == ones
assert P.transpose() * ones == ones
assert P.det() == A.det() * B.det()

obstruction = matrix(R, [[1,0,b],[0,1+b,b],[0,0,1]])
assert obstruction.det() == 1 + b
print("gibson basic doubly stochastic Sage certificate: ok")
