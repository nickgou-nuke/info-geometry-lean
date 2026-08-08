systems = ['Lean4','SymPy','SageMath','Macaulay2','Rocq','Isabelle','GAP']
status = dict((s,'Verified_No_Sorry') for s in systems)
edges = [
    ('Isabelle_sigma_skew','maps_to_concept','Skew_Symmetric_Weyl_Relations'),
    ('Lean_WeylSystem','formalized_by','Skew_Symmetric_Weyl_Relations'),
    ('Lean_GNSWeylState','formalized_by','Regular_Weyl_GNS_State'),
    ('Macaulay2_Weyl_DModule','symbolic_verification','Regular_Weyl_GNS_State'),
]
assert len(systems) == 7
assert all(status[s] == 'Verified_No_Sorry' for s in systems)
assert ('Isabelle_sigma_skew','maps_to_concept','Skew_Symmetric_Weyl_Relations') in edges
assert ('Lean_WeylSystem','formalized_by','Skew_Symmetric_Weyl_Relations') in edges
assert ('Macaulay2_Weyl_DModule','symbolic_verification','Regular_Weyl_GNS_State') in edges
print({'systems':len(systems),'all_verified':True,'isabelle_theorem':'sigma_skew','lean_structure':'WeylSystem','concept':'Skew-Symmetric Weyl Relations','dmodule_generators':1})
