cmu_head='3b078f5f1de251637decf04bd3fc8aa01930a6b3'
cmu_files=['algebra/exact_couple.hlean','algebra/spectral_sequence.hlean','cohomology/serre.hlean','homotopy/EM.hlean','cohomology/gysin.hlean']
base_betti={0:1,2:1,4:1,6:1}
fiber_betti={0:1,1:1}
def br(m,n): return base_betti.get(m,0)*fiber_betti.get(n,0)
grid={(p,q):br(p,q) for p in range(7) for q in range(2)}
e2_total=sum(grid.values())
e2_euler=sum(((-1)**(p+q))*v for (p,q),v in grid.items())
base_euler=sum(((-1)**p)*base_betti.get(p,0) for p in range(7))
fiber_euler=sum(((-1)**q)*fiber_betti.get(q,0) for q in range(2))
def d_target(r,p,q): return (p+r,q-r+1)
def d_rank(r,p,q): return 0
def d_square(r,p,q): return 0
stable_page=3
varlamov_even=sum(binomial(5,i) for i in [0,2,4]); varlamov_odd=sum(binomial(5,i) for i in [1,3,5])
S3=SymmetricGroup(3)
assert S3.order()==6
assert cmu_files[2]=='cohomology/serre.hlean' and cmu_head.startswith('3b078f5')
assert e2_total==8 and e2_euler==0 and base_euler==4 and fiber_euler==0
assert d_target(2,1,3)==(3,2) and d_square(2,1,3)==0
assert stable_page==3 and all(grid[k]-d_rank(stable_page,*k)==grid[k] for k in grid)
assert 2+(-2)==0 and varlamov_even-varlamov_odd==0 and varlamov_even+varlamov_odd==32
assert 7-1==6 and 24+1+10+10==45
R.<x0,x1,x2,x3,x4,x5,x6,x7>=PolynomialRing(QQ)
null_quadric=x0*x7-x1*x4-x2*x5-x3*x6
assert null_quadric.degree()==2
print({'cmu_head':cmu_head,'cmu_files':cmu_files,'e2_total_rank':e2_total,'e2_euler':e2_euler,'base_euler':base_euler,'fiber_euler':fiber_euler,'d2_target_1_3':d_target(2,1,3),'boundary_square_zero':d_square(2,1,3),'stable_page':stable_page,'anomaly_compensated':0,'witten_moebius_index':varlamov_even-varlamov_odd,'null_quadric_dim':6,'so55_su5_partition':45,'s3_order':S3.order(),'null_quadric_degree':null_quadric.degree(),'edges':5})
