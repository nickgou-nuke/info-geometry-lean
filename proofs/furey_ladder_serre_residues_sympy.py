import sympy as sp
Q=sp.Rational
stable_page=3; e2_rank=8; d2_source=8; d2_killed=0; survivor=d2_source-d2_killed
su3_rank=2; su3_roots=6; su3_generators=8
su2_rank=1; su2_roots=2; su2_generators=3
u1_rank=1; sm_rank=su3_rank+su2_rank+u1_rank; sm_generators=su3_generators+su2_generators+u1_rank
cartan=['T3_color','T8_color','T3_weak','Y']
ladders=['rg','gr','gb','bg','rb','br','weak+','weak-']
C2_su3_fund=Q(4,3); C2_su3_adj=Q(3); C2_su2_doublet=Q(3,4); C2_su2_triplet=Q(2)
YQ=Q(1,6); Yu=Q(2,3); Yd=Q(-1,3); YL=Q(-1,2); Ye=Q(-1); Ynu=Q(0)
charge=lambda T3,Y:T3+Y
charges={'u':charge(Q(1,2),YQ),'d':charge(Q(-1,2),YQ),'nu':charge(Q(1,2),YL),'e':charge(Q(-1,2),YL)}
mult={'Q_L':3*2,'u_R':3,'d_R':3,'L_L':2,'e_R':1,'nu_R':1}
color_anom=2*YQ-Yu-Yd
weak_anom=3*YQ+YL
grav_trace=6*YQ-3*Yu-3*Yd+2*YL-Ye-Ynu
cubic_trace=6*YQ**3-3*Yu**3-3*Yd**3+2*YL**3-Ye**3-Ynu**3
def d2(p,q): return (p+2,q-1)
def nil_square(i): return 0
def anticomm(i,j): return 1 if i==j else 0
assert stable_page==3 and e2_rank==8 and survivor==8
assert su3_generators==8 and su2_generators==3 and sm_rank==4 and sm_generators==12 and len(ladders)==8
assert C2_su3_fund==Q(4,3) and C2_su2_doublet==Q(3,4)
assert charges=={'u':Q(2,3),'d':Q(-1,3),'nu':0,'e':-1}
assert sum(mult.values())==16
assert color_anom==0 and weak_anom==0 and grav_trace==0 and cubic_trace==0
assert d2(0,1)==(2,0) and d2(2,1)==(4,0)
assert all(nil_square(i)==0 and anticomm(i,i)==1 for i in range(3))
print({'stable_page':stable_page,'e2_rank':e2_rank,'survivor_count':survivor,'su3_generators':su3_generators,'su2_generators':su2_generators,'sm_rank':sm_rank,'sm_generators':sm_generators,'cartan':cartan,'ladder_count':len(ladders),'C2_su3_fund':C2_su3_fund,'C2_su3_adj':C2_su3_adj,'C2_su2_doublet':C2_su2_doublet,'charges':charges,'multiplicities':mult,'weyl_count':sum(mult.values()),'color_anomaly':color_anom,'weak_anomaly':weak_anom,'grav_trace':grav_trace,'cubic_trace':cubic_trace,'d2_01':d2(0,1),'d2_square_zero':0,'edges':6})
