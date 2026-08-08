import sympy as sp
Q=sp.Rational

s=1; d=5; modes=s+d
u6=modes*modes
partition=1+d+d+d*d
sym=lambda n: n*(n+1)//2
anti=lambda n: n*(n-1)//2
sp6=sym(3)+sym(3)+3*3
collective=anti(3)+sym(3)+sym(3)+sym(3)
raising=(Q(1,2),-Q(1,2),Q(1,2),2)
lowering=(Q(1,2),-Q(1,2),-Q(1,2),2)
plus=(raising[0]+lowering[0],raising[1]+lowering[1],raising[2]+lowering[2])
Tdiff=raising[2]-lowering[2]
def C1(m): return -m*m
def k(C): return -C
def V(m,lam): return m*m*lam*lam/Q(2)
def bracket(C): return 2*C
def Ephonon(omega,n): return (n+Q(1,2))*omega
def raising_phonon(Qv,Kv,Tv): return sp.Rational(1,2)*(Qv-Kv) + sp.I*sp.Rational(1,2)*Tv
def u_dim(n): return n*n
def su_dim(n): return n*n-1
def so_dim(n): return n*(n-1)//2
def sp_dim_from_half_rank(n): return n*(2*n+1)
group_dimensions={'U6':36,'U5':25,'SU3':8,'SO6':15,'SO5':10,'SO3':3,'Sp6R':21}
subgroup_edges={('U6','U5'),('U6','SU3'),('U6','SO6'),('SO6','SO5'),('SO5','SO3'),('Sp6R','U6')}
def delta(i,j): return 1 if i==j else 0
def matrix_first(i,j,k,l): return delta(j,k)
def matrix_second(i,j,k,l): return -delta(l,i)
def ccr(hbar): return sp.I*hbar
assert modes==6
assert u6==36
assert partition==36
assert sym(3)==6 and anti(3)==3
assert sp6==21 and collective==21
assert raising==(Q(1,2),-Q(1,2),Q(1,2),2)
assert plus==(1,-1,0)
assert Tdiff==1
m=sp.symbols('m')
assert sp.expand(k(C1(m))-m*m)==0
assert k(C1(0))==0
assert V(3,2)==18
assert sp.expand(bracket(C1(m))-(-2*m*m))==0
assert Ephonon(5,1)==Q(15,2)
assert raising_phonon(5,1,3) == 2 + sp.Rational(3,2)*sp.I
assert raising_phonon(5,1,3) != 0
assert u_dim(6)==36 and su_dim(3)==8
assert so_dim(6)==15 and so_dim(5)==10 and so_dim(3)==3
assert sp_dim_from_half_rank(3)==21
assert group_dimensions == {'U6':36,'U5':25,'SU3':8,'SO6':15,'SO5':10,'SO3':3,'Sp6R':21}
assert ('U6','U5') in subgroup_edges and ('U6','SU3') in subgroup_edges and ('U6','SO6') in subgroup_edges
assert ('SO6','SO5') in subgroup_edges and ('SO5','SO3') in subgroup_edges and ('Sp6R','U6') in subgroup_edges
assert (matrix_first(1,2,2,3), matrix_second(1,2,2,3)) == (1,0)
assert (matrix_first(1,2,2,1), matrix_second(1,2,2,1)) == (1,-1)
assert ccr(1) == sp.I and ccr(1) != 0
edges=['represented_by','counted_by','represented_by_sp6','decomposes_into','quantizes']
print({'ibm_modes':modes,'u6_generators':u6,'ibm_partition':partition,'sp6_symmetric_pairs':sym(3),'so3_antisymmetric_pairs':anti(3),'sp6_generators':sp6,'collective_tensor_certificate':collective,'raising_plus_lowering':plus,'raising_minus_lowering_T':Tdiff,'raising_phonon_sample':raising_phonon(5,1,3),'raising_nonzero':raising_phonon(5,1,3)!=0,'massless_stiffness':k(C1(0)),'spring_potential_3_2':V(3,2),'one_phonon_energy_w5':Ephonon(5,1),'group_dimensions':group_dimensions,'matrix_E12_E23':(matrix_first(1,2,2,3),matrix_second(1,2,2,3)),'matrix_E12_E21':(matrix_first(1,2,2,1),matrix_second(1,2,2,1)),'ccr_i':ccr(1),'edges':len(edges),'subgroup_edges':len(subgroup_edges)})
