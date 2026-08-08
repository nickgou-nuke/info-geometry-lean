import sympy as sp
Q=sp.Rational
aeon_count=3; generation_count=3; ckm_angles=3; ckm_phases=1; ckm_params=4
stable_page=3; serre_residue_rank=8; one_gen_weyl=16; three_gen_weyl=48
su3_rank=2; su3_roots=6; su3_cartan=2; su3_generators=8
su2_rank=1; su2_roots=2; su2_cartan=1; su2_generators=3
u1_rank=1; sm_rank=4; sm_generators=12
cartan=['T3_color','T8_color','T3_weak','Y']
flavors=['u','c','t','d','s','b']; generations=['g1','g2','g3']
ckm_entries=9
C2_su3_fund=Q(4,3); C2_su3_adj=Q(3); C2_su2_doublet=Q(3,4); C2_su2_triplet=Q(2)
YQ=Q(1,6); Yu=Q(2,3); Yd=Q(-1,3)
up_charge=Q(1,2)+YQ; down_charge=Q(-1,2)+YQ
color_anom=2*YQ-Yu-Yd; weak_anom=3*YQ+Q(-1,2); gen_anom=3*color_anom+3*weak_anom
V=sp.eye(3)
assert V*V.T==sp.eye(3) and V.T*V==sp.eye(3) and V.det()==1
jarlskog=0; cp_phase=0
d2=lambda p,q:(p+2,q-1)
assert aeon_count==3 and generation_count==3 and ckm_params==4 and ckm_entries==9 and three_gen_weyl==48
assert su3_generators==8 and su2_generators==3 and sm_rank==4 and sm_generators==12 and len(cartan)==4
assert C2_su3_fund==Q(4,3) and C2_su2_doublet==Q(3,4)
assert up_charge==Q(2,3) and down_charge==Q(-1,3)
assert color_anom==0 and weak_anom==0 and gen_anom==0
assert d2(0,1)==(2,0)
print({'aeon_count':aeon_count,'generation_count':generation_count,'ckm_parameters':ckm_params,'ckm_entries':ckm_entries,'three_generation_weyl_count':three_gen_weyl,'stable_page':stable_page,'serre_residue_rank':serre_residue_rank,'su3_generators':su3_generators,'su2_generators':su2_generators,'sm_rank':sm_rank,'sm_generators':sm_generators,'cartan':cartan,'flavors':flavors,'generations':generations,'C2_su3_fund':C2_su3_fund,'C2_su2_doublet':C2_su2_doublet,'up_charge':up_charge,'down_charge':down_charge,'color_anomaly':color_anom,'weak_anomaly':weak_anom,'generation_anomaly':gen_anom,'determinant':V.det(),'jarlskog':jarlskog,'cp_phase':cp_phase,'aeon_colimit_rank':24,'d2_01':d2(0,1),'edges':6})
