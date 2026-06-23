#!/usr/bin/env sage
A = Matrix(QQ, [[1,0],[0,-1]])
B = Matrix(QQ, [[1,1],[0,1]])
Ainv = A
Binv = Matrix(QQ, [[1,-1],[0,1]])
I = identity_matrix(QQ, 2)
assert A*Ainv == I
assert B*Binv == I
assert Binv*B == I
assert A*B*Ainv == Binv
assert A*B*Ainv*B == I
print("projective Klein compactification Sage certificate: ok")
