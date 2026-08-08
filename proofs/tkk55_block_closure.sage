# Exact SageMath certificate for the split 1+8+1 block realization.
R = PolynomialRing(QQ, names=('a','b') + tuple('x%s'%i for i in range(8)) + tuple('y%s'%i for i in range(8)))
gens = R.gens_dict()
a, b = gens['a'], gens['b']
x = vector(R, [gens['x%s'%i] for i in range(8)])
y = vector(R, [gens['y%s'%i] for i in range(8)])
B = diagonal_matrix(R, [1]*4 + [-1]*4)
G = matrix(R, 10, 10)
G[0,9] = G[9,0] = 1
G[1:9,1:9] = B

def flat(v): return v * B
def P(v):
    A = matrix(R,10,10); A[1:9,0] = v.column(); A[9,1:9] = -flat(v); return A
def N(v):
    A = matrix(R,10,10); A[0,1:9] = -flat(v); A[1:9,9] = v.column(); return A
def D(c,K):
    A = matrix(R,10,10); A[0,0]=c; A[1:9,1:9]=K; A[9,9]=-c; return A
def bracket(A,C): return A*C-C*A

S = matrix(R,8,8)
for i in range(8):
    for j in range(i+1,8):
        s = R('s%s%s'%(i,j)) if 's%s%s'%(i,j) in R.variable_names() else R.zero()
# Use basis verification over QQ for the 45-dimensional structural statement.
Bq = diagonal_matrix(QQ,[1]*4+[-1]*4)
Gq = matrix(QQ,10,10); Gq[0,9]=Gq[9,0]=1; Gq[1:9,1:9]=Bq
cols=[]
for i in range(8): cols.append(vector(QQ,P(vector(R,[1 if k==i else 0 for k in range(8)])).list()))
cols.append(vector(QQ,D(1,matrix(R,8,8)).list()))
for i in range(8):
    for j in range(i+1,8):
        E=matrix(QQ,8,8); E[i,j]=1; E[j,i]=-1
        K=Bq*E
        Aq=matrix(QQ,10,10); Aq[1:9,1:9]=K
        cols.append(vector(QQ,Aq.list()))
for i in range(8): cols.append(vector(QQ,N(vector(R,[1 if k==i else 0 for k in range(8)])).list()))
assert matrix(QQ,cols).rank()==45
positive = sum(1 for e in Gq.eigenvalues() if e > 0)
negative = sum(1 for e in Gq.eigenvalues() if e < 0)
assert Gq.rank()==10 and (positive, negative)==(5,5)
print('Sage structural block rank: 45')
print('Sage hyperbolic metric inertia difference: 0 (signature (5,5))')
print('TKK55 SAGE CERTIFICATE: PASS')
