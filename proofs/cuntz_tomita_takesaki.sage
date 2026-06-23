#!/usr/bin/env sage
c = QQ(5)/4
s = QQ(3)/4
I = identity_matrix(QQ, 2)
Pp = Matrix(QQ, [[1,0],[0,0]])
Pm = Matrix(QQ, [[0,0],[0,1]])
eta = Pp - Pm
L = c*I - s*eta
R = c*I + s*eta
assert Pp + Pm == I
assert Pp*Pp == Pp
assert Pm*Pm == Pm
assert Pp*Pm == zero_matrix(QQ,2)
assert Pm*Pp == zero_matrix(QQ,2)
assert eta*eta == I
assert c*c - s*s == 1
assert L*R == I
assert R*L == I
# Basis check proves linear identity S(X)=X^T.
for i in range(2):
    for j in range(2):
        X = zero_matrix(QQ,2)
        X[i,j] = 1
        Delta = L*X*R
        S = L*Delta.transpose()*R
        assert S == X.transpose()
print("cuntz Tomita-Takesaki Sage certificate: ok")
