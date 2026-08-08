Q=QQ
n=5
null_dim=2*n
so_dim=null_dim*(null_dim-1)//2
matrix_dim=n*n
sl5=matrix_dim-1
skew=n*(n-1)//2
partition=sl5+1+skew+skew
block=matrix_dim+skew+skew
spin_even=binomial(5,0)+binomial(5,2)+binomial(5,4)
spin_odd=binomial(5,1)+binomial(5,3)+binomial(5,5)
def involution(diag,off): return (diag,-off)
def mobius_inv(e,o): return ((e+o)/Q(2),(e-o)/Q(2))
def mobius_rec(x,y): return (x+y,x-y)
def klein_avg(a,b,c,d): return Q(1)/4*(a+b+c+d)
def trip_poly(d): return d*(d-1)*(d+1)
def C1(m): return -m*m
def kspring(C): return -C
def brillouin(k): return (k,-k)
def klein_mode(k): return sum(brillouin(k))
eta=zero_matrix(QQ,10); eta[0:5,5:10]=identity_matrix(QQ,5); eta[5:10,0:5]=identity_matrix(QQ,5)
assert eta.transpose()==eta and eta*eta==identity_matrix(QQ,10)
R=PolynomialRing(QQ, ['a'+str(i)+str(j) for i in range(5) for j in range(5)] + ['b'+str(i)+str(j) for i in range(5) for j in range(i+1,5)] + ['c'+str(i)+str(j) for i in range(5) for j in range(i+1,5)])
gens=R.gens(); idx=0
A=matrix(R,5,5,lambda i,j: gens[i*5+j]); idx=25
B=zero_matrix(R,5); C=zero_matrix(R,5)
for i in range(5):
 for j in range(i+1,5):
  b=gens[idx]; idx+=1; B[i,j]=b; B[j,i]=-b
for i in range(5):
 for j in range(i+1,5):
  c=gens[idx]; idx+=1; C[i,j]=c; C[j,i]=-c
X=block_matrix([[A,B],[C,-A.transpose()]])
etaR=matrix(R,eta)
assert X.transpose()*etaR + etaR*X == zero_matrix(R,10)
assert null_dim==10 and so_dim==45 and sl5==24 and skew==10 and partition==45 and block==45
assert spin_even==16 and spin_odd==16 and spin_even+spin_odd==32
assert involution(*involution(Q(7)/3,Q(5)/2))==(Q(7)/3,Q(5)/2)
assert mobius_rec(*mobius_inv(Q(7),Q(3)))==(Q(7),Q(3))
assert klein_avg(1,2,3,4)==Q(5)/2
assert [trip_poly(Q(x)) for x in [-1,0,1]]==[0,0,0]
S.<m>=PolynomialRing(QQ)
assert kspring(C1(m))-m*m==0
assert klein_mode(Q(11)/7)==0
edges=['decomposes_to','trace_splits_to','skew_splits_to_B','skew_splits_to_C','quotients_modes']
print({'null_dim':null_dim,'so55_dim':so_dim,'sl5_adj':sl5,'dilaton':1,'skew10':skew,'partition':partition,'eta_involutive':eta*eta==identity_matrix(QQ,10),'block_constraint_zero':True,'spin_even16':spin_even,'spin_odd16':spin_odd,'mobius_roundtrip':True,'klein_average':klein_avg(1,2,3,4),'tripotent_roots':[-1,0,1],'brillouin_cancel':klein_mode(Q(11)/7),'edges':len(edges)})
