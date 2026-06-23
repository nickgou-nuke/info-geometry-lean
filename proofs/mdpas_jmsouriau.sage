# Exact-rational Sage certificate for Souriau MDPAS 1974 finite spin layer.
R = PolynomialRing(QQ, 'p0,p1,p2,p3,u0,u1,u2,u3,v0,v1,v2,v3,f01,f02,f03,f12,f13,f23,m,q,sB')
(p0,p1,p2,p3,u0,u1,u2,u3,v0,v1,v2,v3,f01,f02,f03,f12,f13,f23,m,q,sB) = R.gens()
P = vector(R, [p0,p1,p2,p3])
U = vector(R, [u0,u1,u2,u3])
V = vector(R, [v0,v1,v2,v3])

def dot(a,b):
    return sum(a[i]*b[i] for i in range(4))

def wedge(a,b):
    return matrix(R, 4, 4, lambda i,j: a[i]*b[j] - a[j]*b[i])

S = wedge(U,V)
assert S + S.transpose() == 0
assert wedge(U,V) + wedge(V,U) == 0
C = S * P
expected = vector(R, [U[i]*dot(V,P) - V[i]*dot(U,P) for i in range(4)])
assert C == expected
F = matrix(R, [[0,f01,f02,f03],[-f01,0,f12,f13],[-f02,-f12,0,f23],[-f03,-f13,-f23,0]])
assert F + F.transpose() == 0
assert dot(P, F*P) == 0

def pfaffian4(A):
    return A[0,1]*A[2,3] - A[0,2]*A[1,3] + A[0,3]*A[1,2]

assert pfaffian4(S) == 0
EM = matrix(R, [[0,f01,f02,f03],[-f01,0,-f23,f13],[-f02,f23,0,-f12],[-f03,-f13,f12,0]])
assert EM + EM.transpose() == 0
assert pfaffian4(EM) == -(f01*f12 + f02*f13 + f03*f23)
assert 2*q*sB/(2*m) == q*sB/m
assert 2*(m/2) == m
print('mdpas JMSouriau Sage certificate: ok')
