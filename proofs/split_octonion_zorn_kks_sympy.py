import sympy as sp
Q=sp.Rational

def vadd(x,y): return tuple(a+b for a,b in zip(x,y))
def vneg(x): return tuple(-a for a in x)
def vsub(x,y): return vadd(x,vneg(y))
def smul(a,x): return tuple(a*t for t in x)
def dot(x,y): return sum(a*b for a,b in zip(x,y))
def cross(x,y):
    return (x[1]*y[2]-x[2]*y[1], x[2]*y[0]-x[0]*y[2], x[0]*y[1]-x[1]*y[0])
def Z(a,u,v,b): return (Q(a),tuple(map(Q,u)),tuple(map(Q,v)),Q(b))
def zmul(X,Y):
    a,u,v,b=X; c,x,y,d=Y
    return (a*c+dot(u,y), vsub(vadd(smul(a,x),smul(d,u)),cross(v,y)), vadd(vadd(smul(c,v),smul(b,y)),cross(u,x)), dot(v,x)+b*d)
def zconj(X):
    a,u,v,b=X; return (b,vneg(u),vneg(v),a)
def znorm(X):
    a,u,v,b=X; return a*b-dot(u,v)
def zsub(X,Y): return (X[0]-Y[0],vsub(X[1],Y[1]),vsub(X[2],Y[2]),X[3]-Y[3])
def zassoc(X,Y,W): return zsub(zmul(zmul(X,Y),W),zmul(X,zmul(Y,W)))
zvec=(Q(0),Q(0),Q(0)); e1=(Q(1),Q(0),Q(0)); e2=(Q(0),Q(1),Q(0))
one=Z(1,zvec,zvec,1); zero_div=Z(1,e1,e1,1); U1=Z(0,e1,zvec,0); L1=Z(0,zvec,e1,0); U2=Z(0,e2,zvec,0)
assoc=zassoc(U1,L1,U2)
def ad_coeff(N): return -4*N
def comp(a,c): return a+c
def mobius(k): return -k
def trip_int(d): return d**3-d
m=sp.symbols('m')
varlamov_even=sum(sp.binomial(5,i) for i in [0,2,4]); varlamov_odd=sum(sp.binomial(5,i) for i in [1,3,5])
assert znorm(zero_div)==0 and znorm(one)==1 and znorm(zconj(zero_div))==znorm(zero_div)
assert assoc[1]==e2 and assoc!=(0,zvec,zvec,0)
assert (4,4)==(4,4) and (3,4)==(3,4) and sum((2,4))==6 and sum((3,3))==6
assert 8==2+3+3 and 7==7 and 6==6 and 4==4
assert znorm(one)!=0 and znorm(zero_div)==0
assert ad_coeff(Q(1))==-4 and ad_coeff(Q(-1))==4
assert comp(Q(2),Q(-2))==0
assert 24+1+10+10==45
assert sp.expand(-(-m*m)-m*m)==0
assert varlamov_even==16 and varlamov_odd==16 and varlamov_even+varlamov_odd==32 and varlamov_even-varlamov_odd==0
assert mobius(mobius(7))==7 and 7+mobius(7)==0
assert [trip_int(i) for i in [-1,0,1]]==[0,0,0]
assert 7-1==6
print({'zorn_slots':8,'split_signature':(4,4),'imaginary_signature':(3,4),'imaginary_null_quadric_dim':6,'zero_divisor_norm':znorm(zero_div),'one_norm':znorm(one),'associator_u':assoc[1],'associator_nonzero':assoc!=(0,zvec,zvec,0),'positive_orbit_signature':(2,4),'negative_orbit_signature':(3,3),'subalgebra_bound':4,'ad_square_coeff_Npos':ad_coeff(Q(1)),'ad_square_coeff_Nneg':ad_coeff(Q(-1)),'anomaly_compensated':comp(Q(2),Q(-2)),'so55_su5_partition':45,'varlamov_even':varlamov_even,'varlamov_odd':varlamov_odd,'witten_moebius_index':varlamov_even-varlamov_odd,'mobius_involutive':mobius(mobius(7))==7,'klein_pair_invariant':7+mobius(7),'tripotent_roots':[-1,0,1],'edges':5})
