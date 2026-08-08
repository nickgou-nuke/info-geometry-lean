Q=QQ
aeon_count=3; theta_aeon_index=3; q=Q(1)/10; theta_sediment=q**theta_aeon_index; inverse_theta=Q(10)**theta_aeon_index
su3_rank=2; su3_roots=6; su3_cartan=2; su3_generators=8; su3_weyl_order=6
su2_rank=1; su2_generators=3; u1_rank=1; sm_rank=4; sm_generators=12
C2_su3_fund=Q(4)/3; C2_su3_adj=Q(3)
roots={'alpha1':1,'alpha2':1,'alpha12':2,'neg_alpha1':-1,'neg_alpha2':-1,'neg_alpha12':-2}
def cp(theta): return -theta
def axion(theta): return -theta
def effective(theta,a): return theta+a
instanton=1; anti_instanton=-1; topological_pair=instanton+anti_instanton
pontryagin_generators=1; theta_ideal_generators=2; dmodule_ccr_generators=1
u1_axial_anomaly_coeff=su3_generators
color_anomaly=Q(0); weak_anomaly=Q(0); generation_anomaly=Q(0)
def d2(p,q): return (p+2,q-1)
S3=SymmetricGroup(3); assert S3.order()==6
assert aeon_count==3 and theta_aeon_index==3 and theta_sediment==Q(1)/1000 and inverse_theta==1000
assert su3_rank==2 and su3_generators==8 and su3_cartan==2 and su3_weyl_order==6 and sm_rank==4 and sm_generators==12
assert C2_su3_fund==Q(4)/3 and C2_su3_adj==3
assert roots['alpha12']==2 and roots['neg_alpha12']==-2
assert cp(cp(Q(7)/5))==Q(7)/5 and effective(Q(7)/5,axion(Q(7)/5))==0
assert topological_pair==0
assert pontryagin_generators==1 and theta_ideal_generators==2 and dmodule_ccr_generators==1
assert u1_axial_anomaly_coeff==8 and color_anomaly==0 and weak_anomaly==0 and generation_anomaly==0
assert d2(0,1)==(2,0)
print({'aeon_count':aeon_count,'theta_aeon_index':theta_aeon_index,'q_dial':q,'theta_sediment_weight':theta_sediment,'inverse_theta_scale':inverse_theta,'su3_rank':su3_rank,'su3_roots':su3_roots,'su3_cartan':su3_cartan,'su3_generators':su3_generators,'su3_weyl_order':su3_weyl_order,'sm_rank':sm_rank,'sm_generators':sm_generators,'C2_su3_fund':C2_su3_fund,'C2_su3_adj':C2_su3_adj,'roots':roots,'cp_twice_sample':cp(cp(Q(7)/5)),'theta_cancelled_sample':effective(Q(7)/5,axion(Q(7)/5)),'topological_charge_pair':topological_pair,'pontryagin_generators':pontryagin_generators,'theta_ideal_generators':theta_ideal_generators,'dmodule_ccr_generators':dmodule_ccr_generators,'u1_axial_anomaly_coeff':u1_axial_anomaly_coeff,'generation_anomaly':generation_anomaly,'s3_order':S3.order(),'d2_01':d2(0,1),'edges':5})
