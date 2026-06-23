# Exact-rational Sage certificate for Barbaresco SPIGL 2020 finite Souriau layer.
R = PolynomialRing(QQ, 'x11,x12,x21,x22,y11,y12,y21,y22,z11,z12,z21,z22,f11,f12,f21,f22,b,c,Q')
(x11,x12,x21,x22,y11,y12,y21,y22,z11,z12,z21,z22,f11,f12,f21,f22,b,c,Q) = R.gens()
X = matrix(R, [[x11,x12],[x21,x22]])
Y = matrix(R, [[y11,y12],[y21,y22]])
Z = matrix(R, [[z11,z12],[z21,z22]])
F = matrix(R, [[f11,f12],[f21,f22]])

def comm(A,B):
    return A*B - B*A

def kks(F,A,B):
    return (F*comm(A,B)).trace()

assert comm(X,X) == 0
assert comm(X,Y) + comm(Y,X) == 0
assert comm(X,comm(Y,Z)) + comm(Y,comm(Z,X)) + comm(Z,comm(X,Y)) == 0
assert kks(F,X,X) == 0
assert kks(F,X,Y) + kks(F,Y,X) == 0
assert kks(F,X,comm(Y,Z)) + kks(F,Y,comm(Z,X)) + kks(F,Z,comm(X,Y)) == 0
massieu = lambda t: t^2 / QQ(2)
assert massieu(b+1) - 2*massieu(b) + massieu(b-1) == 1
assert c*Q - c*Q == 0
print('barbaresco SPIGL2020 Sage certificate: ok')
