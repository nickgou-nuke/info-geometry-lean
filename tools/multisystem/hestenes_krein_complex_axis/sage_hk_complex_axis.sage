# Exact SageMath verifier for the Hestenes/Krein complex axis packet.
R = PolynomialRing(QQ, 'a,b,c,d,p,q')
a,b,c,d,p,q = R.gens()
M = MatrixSpace(R, 2, 2)
I2 = M.identity_matrix()
K = M([[0,-1],[1,0]])
J = M([[0,1],[1,0]])
eps = M([[1,0],[0,-1]])
assert K*K == -I2
assert J*J == I2
assert eps*eps == I2
assert J*eps == K
assert eps*J == -K
assert K.trace() == 0
rho1 = a*I2 + b*K
rho2 = c*I2 + d*K
rho_prod = (a*c - b*d)*I2 + (a*d + b*c)*K
assert rho1*rho2 == rho_prod
A = M([[p,q],[-q,p]])
assert K*A == A*K
print('SAGE_HK_COMPLEX_AXIS_OK')
