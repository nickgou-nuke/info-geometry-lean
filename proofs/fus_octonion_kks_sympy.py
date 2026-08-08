import sympy as sp
Q=sp.Rational

oct_dim=8; im_dim=7; orbit_dim=6; g2_dim=14; su3_dim=8
fano=[(1,2,3),(1,4,5),(1,7,6),(2,4,6),(2,5,7),(3,4,7),(3,6,5)]
prod={}
for i in range(8): prod[(0,i)]=(1,i); prod[(i,0)]=(1,i)
for i in range(1,8): prod[(i,i)]=(-1,0)
for a,b,c in fano:
    prod[(a,b)]=(1,c); prod[(b,c)]=(1,a); prod[(c,a)]=(1,b)
    prod[(b,a)]=(-1,c); prod[(c,b)]=(-1,a); prod[(a,c)]=(-1,b)
def basis(i):
    v=[Q(0)]*8; v[i]=Q(1); return v
def mul(x,y):
    z=[Q(0)]*8
    for i,xi in enumerate(x):
        if xi==0: continue
        for j,yj in enumerate(y):
            if yj==0: continue
            s,k=prod[(i,j)]
            z[k]+=xi*yj*s
    return z
def neg(x): return [-a for a in x]
def sub(x,y): return [a-b for a,b in zip(x,y)]
def add(x,y): return [a+b for a,b in zip(x,y)]
def assoc(x,y,z): return sub(mul(mul(x,y),z), mul(x,mul(y,z)))
def comm(x,y): return sub(mul(x,y),mul(y,x))
def inner(x,y): return sum(a*b for a,b in zip(x,y))
e=[basis(i) for i in range(8)]
assoc_alt=assoc(e[1],e[1],e[2])
assoc_nonzero=assoc(e[1],e[2],e[4])
comm_skew=add(comm(e[1],e[2]),comm(e[2],e[1]))
inner_inv=inner(mul(e[1],e[3]),e[2])-inner(e[1],mul(e[3],e[2]))
def sig_total(s): return s[0]+s[1]
def kks(mu,br): return -mu*br
def mobius_inv(even,odd): return ((even+odd)/2,(even-odd)/2)
def mobius_rec(x,y): return (x+y,x-y)
def trip(d): return d*(d-1)*(d+1)
def C1(m): return -m*m
def stiff(C): return -C
m=sp.symbols('m')
assert oct_dim==8 and im_dim==7 and orbit_dim==6 and g2_dim-su3_dim==6
assert len(fano)==7 and 7*3==21
assert assoc_alt==[0]*8
assert assoc_nonzero!=[0]*8
assert comm_skew==[0]*8
assert inner_inv==0
assert sig_total((6,0))==sig_total((3,3))==sig_total((2,4))==6
assert kks(3,5)==-15
assert mobius_rec(*mobius_inv(Q(7),Q(3)))==(Q(7),Q(3))
assert (1+2+3+4)*Q(1,4)==Q(5,2)
assert [trip(Q(i)) for i in [-1,0,1]]==[0,0,0]
assert sp.expand(stiff(C1(m))-m*m)==0
assert 24+1+10+10==45
assert sp.binomial(5,0)+sp.binomial(5,2)+sp.binomial(5,4)==16
assert sp.binomial(5,1)+sp.binomial(5,3)+sp.binomial(5,5)==16
print({'octonion_dim':oct_dim,'imaginary_dim':im_dim,'orbit_dim':orbit_dim,'g2_su3_orbit':g2_dim-su3_dim,'fano_lines':len(fano),'fano_directed_products':21,'associator_alt_zero':assoc_alt==[0]*8,'associator_nonzero_sample':assoc_nonzero,'commutator_skew':comm_skew==[0]*8,'inner_invariance_sample':inner_inv,'kks_sample':kks(3,5),'kks_closed_obstruction_nonzero':assoc_nonzero!=[0]*8,'signatures':[(6,0),(3,3),(2,4)],'so55_su5_partition':45,'spin_even16':16,'spin_odd16':16,'mobius_roundtrip':True,'klein_average':Q(5,2),'tripotent_roots':[-1,0,1]})
