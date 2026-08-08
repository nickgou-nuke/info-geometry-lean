Q=QQ
aeon_count=3; generation_count=3; vintage_count=3; modular_transitions=2
stable_page=3; serre_residue_rank=8; aeon_colimit_rank=24; one_gen_weyl=16; three_gen_weyl=48
su3_rank=2; su3_generators=8; su2_rank=1; su2_generators=3; u1_rank=1; sm_rank=4; sm_generators=12; cartan_generators=4
cartan=['T3_color','T8_color','T3_weak','Y']
C2_su3_fund=Q(4)/3; C2_su3_adj=Q(3); C2_su2_doublet=Q(3)/4; C2_su2_triplet=Q(2)
vintages={'must':1,'vintage':2,'reserve':3}
flavor_generation={'u':1,'d':1,'e':1,'c':2,'s':2,'mu':2,'t':3,'b':3,'tau':3}
q=Q(1)/10
def aging(n): return q**n
def inverse(n): return Q(10)**n
mass_ratios={'g2_g1':inverse(2)/inverse(1),'g3_g2':inverse(3)/inverse(2),'g3_g1':inverse(3)/inverse(1)}
def moebius(k): return -k
def round_trip(k): return moebius(moebius(k))
def d2(p,q): return (p+2,q-1)
ckm_angles=3; ckm_phases=1; ckm_params=4; ckm_entries=9
YQ=Q(1)/6; Yu=Q(2)/3; Yd=Q(-1)/3; YL=Q(-1)/2
color_anom=2*YQ-Yu-Yd; weak_anom=3*YQ+YL; gen_anom=3*color_anom+3*weak_anom
S3=SymmetricGroup(3); assert S3.order()==6
assert aeon_count==3 and generation_count==3 and aeon_colimit_rank==24 and three_gen_weyl==48
assert su3_generators==8 and su2_generators==3 and sm_rank==4 and sm_generators==12 and cartan_generators==4
assert C2_su3_fund==Q(4)/3 and C2_su2_doublet==Q(3)/4
assert aging(1)==Q(1)/10 and aging(2)==Q(1)/100 and aging(3)==Q(1)/1000
assert mass_ratios=={'g2_g1':10,'g3_g2':10,'g3_g1':100}
assert round_trip(7)==7 and d2(0,1)==(2,0)
assert ckm_params==4 and ckm_entries==9
assert color_anom==0 and weak_anom==0 and gen_anom==0
print({'aeon_count':aeon_count,'generation_count':generation_count,'vintage_count':vintage_count,'stable_page':stable_page,'serre_residue_rank':serre_residue_rank,'aeon_colimit_rank':aeon_colimit_rank,'three_generation_weyl_count':three_gen_weyl,'su3_generators':su3_generators,'su2_generators':su2_generators,'sm_rank':sm_rank,'sm_generators':sm_generators,'cartan_generators':cartan_generators,'cartan':cartan,'C2_su3_fund':C2_su3_fund,'C2_su2_doublet':C2_su2_doublet,'vintages':vintages,'flavor_generation':flavor_generation,'q_dial':q,'aging_weights':[aging(1),aging(2),aging(3)],'mass_ratios':mass_ratios,'moebius_round_trip':round_trip(7),'d2_01':d2(0,1),'ckm_parameters':ckm_params,'ckm_entries':ckm_entries,'color_anomaly':color_anom,'weak_anomaly':weak_anom,'generation_anomaly':gen_anom,'s3_order':S3.order(),'edges':5})
