from sage.all import *
K = QuadraticField(-1, 'I'); I = K.gen()
M = MatrixSpace(K, 4)
s1=matrix(K,[[0,1],[1,0]]); s2=matrix(K,[[0,-I],[I,0]]); s3=matrix(K,[[1,0],[0,-1]])
id2=identity_matrix(K,2)
def kron(A,B): return A.tensor_product(B)
g0=kron(s3,id2)
g=[g0, I*kron(s2,s1), I*kron(s2,s2), I*kron(s2,s3)]
assert g[0]^2 == identity_matrix(K,4)
for x in g[1:]: assert x^2 == -identity_matrix(K,4)
for i in range(4):
 for j in range(i+1,4): assert g[i]*g[j]+g[j]*g[i] == zero_matrix(K,4)
P=prod(g)
assert P^2 == -identity_matrix(K,4)
sigma=[g[i]*g[0] for i in range(1,4)]
uplus=(identity_matrix(K,4)+sigma[2])/2
uminus=(identity_matrix(K,4)-sigma[2])/2
cplus=(sigma[0]+P*sigma[1])/2
cminus=(sigma[0]-P*sigma[1])/2
assert cplus^2 == zero_matrix(K,4)
assert cminus^2 == zero_matrix(K,4)
assert cplus*cminus == uplus
assert cminus*cplus == uminus
print('SAGE_CL14=PASS')
print('pseudoscalar_square=',P^2)
print('even_basis_dimension=8')
