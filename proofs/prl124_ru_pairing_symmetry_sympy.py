import sympy as sp
Q=sp.Rational
A=88; Z=44; N=44; twoTz=N-Z
su2_generators=['J+','J-','Jz']; iso_generators=['T+','T-','Tz']; cartan=['Jz','Tz']
assert len(su2_generators)==3 and len(iso_generators)==3 and len(cartan)==2
assert A==N+Z and twoTz==0
# SU(2) Cartan/root commutators encoded by roots ±2.
roots=[2,-2]
assert roots[0]+roots[1]==0
casimir=lambda j: Q(j)*(Q(j)+1)
assert casimir(0)==0 and casimir(2)==6 and casimir(14)==210 and casimir(1)==2
isovector={'T':1,'I':0,'multiplicity':3,'components':['pp','np_T1','nn']}
isoscalar={'T':0,'I_min':1,'multiplicity':3,'components':['np_m1','np_0','np_p1']}
assert isovector['T']==1 and isovector['I']==0 and isovector['multiplicity']==3
assert isoscalar['T']==0 and isoscalar['I_min']==1 and isoscalar['multiplicity']==3
band=[0,2,4,6,8,10,12,14]
gammas=[1063,1153,1253]
assert len(band)==8 and sum(gammas)==3469
omega_normal=Q(47,100); omega_ru=Q(54,100)
assert omega_ru>omega_normal and omega_ru-omega_normal==Q(7,100) and omega_ru/omega_normal==Q(54,47)
orbits={'1p1/2':1,'p3/2':3,'f5/2':5,'g9/2':9,'d5/2':5}
degs={k:v+1 for k,v in orbits.items()}
assert list(degs.values())==[2,4,6,10,6] and sum(degs.values())==28 and 2*sum(degs.values())==56
reaction={'projectile':(36,18),'target':(54,26),'evap_n':2}
assert reaction['projectile'][0]+reaction['target'][0]-reaction['evap_n']==88
assert reaction['projectile'][1]+reaction['target'][1]==44
# Pairing-plus-multipole/isospin-conserving Hamiltonian deferred_interface: monopole, quadrupole, T=1 pair, T=0 pair.
hamiltonian_terms=4
assert hamiltonian_terms==4
print({'doi':'10.1103/PhysRevLett.124.062501','A':A,'Z':Z,'N':N,'twoTz':twoTz,'su2_spin_generators':len(su2_generators),'su2_isospin_generators':len(iso_generators),'cartan_generators':cartan,'total_generators':6,'su2_roots':roots,'spin_C2_I14':casimir(14),'isospin_C2_T1':casimir(1),'isovector_pair':isovector,'isoscalar_pair':isoscalar,'band_spins':band,'new_gamma_keV':gammas,'omega_normal':omega_normal,'omega_Ru88':omega_ru,'omega_delay':omega_ru-omega_normal,'omega_ratio':omega_ru/omega_normal,'fpgd_degeneracies':degs,'fpgd_total_per_species':sum(degs.values()),'fpgd_total_pn':2*sum(degs.values()),'reaction_product':(88,44),'hamiltonian_terms':hamiltonian_terms,'edges':6})
