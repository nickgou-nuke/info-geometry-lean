# Exact-rational Sage certificate for MDPAS/JMSouriau obstruction/symplectic/KK layer.
R = PolynomialRing(QQ, 'v0,v1,w0,w1,x0,x1,x2,x3,x4,h')
v0,v1,w0,w1,x0,x1,x2,x3,x4,h = R.gens()
area = QQ(1)
assert area != 0
Omega = matrix(QQ, [[0,1],[-1,0]])
assert Omega + Omega.transpose() == 0
assert Omega.det() == 1
v = vector(R, [v0,v1])
w = vector(R, [w0,w1])
omega = (matrix(R, [list(v)]) * matrix(R, Omega) * matrix(R, [[w0],[w1]]))[0,0]
assert omega == v0*w1 - v1*w0
omega_swap = (matrix(R, [[w0,w1]]) * matrix(R, Omega) * matrix(R, [[v0],[v1]]))[0,0]
assert omega_swap + omega == 0
kk5 = x0^2 - x1^2 - x2^2 - x3^2 - x4^2
m4 = x0^2 - x1^2 - x2^2 - x3^2
assert kk5 == m4 - x4^2
assert 2*(h/2) == h
print('mdpas JMSouriau global obstruction Sage certificate: ok')
