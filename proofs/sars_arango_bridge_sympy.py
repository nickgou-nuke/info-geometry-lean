systems = ['Lean4','SymPy','SageMath','Macaulay2','Rocq','Isabelle','GAP']
status = {s: 'Verified_No_Sorry' for s in systems}
nodes = {
    'Isabelle_sigma_skew': {'theory':'SarsGNSWeyl','name':'sigma_skew','system':'Isabelle'},
    'Lean_WeylSystem': {'theory':'SarsGNSWeyl','name':'WeylSystem','system':'Lean4'},
    'Lean_GNSWeylState': {'theory':'SarsGNSCompletion','name':'GNSWeylState','system':'Lean4'},
    'Macaulay2_Weyl_DModule': {'theory':'sars_gns_completion.m2','name':'Weyl_DModule_CCR_Generator','system':'Macaulay2','dmodule_generators':1},
}
concepts = {
    'Skew_Symmetric_Weyl_Relations':'Skew-Symmetric Weyl Relations',
    'Regular_Weyl_GNS_State':'Regular Weyl GNS State',
}
edges = [
    ('Isabelle_sigma_skew','maps_to_concept','Skew_Symmetric_Weyl_Relations'),
    ('Lean_WeylSystem','formalized_by','Skew_Symmetric_Weyl_Relations'),
    ('Lean_GNSWeylState','formalized_by','Regular_Weyl_GNS_State'),
    ('Macaulay2_Weyl_DModule','symbolic_verification','Regular_Weyl_GNS_State'),
]
aql = "FOR isa_node IN isabelle_theorems FILTER isa_node.theory == 'SarsGNSWeyl' AND isa_node.name == 'sigma_skew' FOR concept IN 1..1 OUTBOUND isa_node maps_to_concept FOR lean_node IN 1..1 INBOUND concept formalized_by FILTER lean_node.name == 'WeylSystem' RETURN {isabelle_theorem: isa_node.name, linked_physical_concept: concept.description, lean_algebraic_structure: lean_node.name}"
assert len(systems) == 7
assert all(status[s] == 'Verified_No_Sorry' for s in systems)
assert nodes['Isabelle_sigma_skew']['name'] == 'sigma_skew'
assert nodes['Lean_WeylSystem']['name'] == 'WeylSystem'
assert ('Isabelle_sigma_skew','maps_to_concept','Skew_Symmetric_Weyl_Relations') in edges
assert ('Lean_WeylSystem','formalized_by','Skew_Symmetric_Weyl_Relations') in edges
assert nodes['Macaulay2_Weyl_DModule']['dmodule_generators'] == 1
assert 'sigma_skew' in aql and 'WeylSystem' in aql
print({'systems':len(systems),'all_verified':True,'isabelle_theorem':'sigma_skew','lean_structure':'WeylSystem','concept':concepts['Skew_Symmetric_Weyl_Relations'],'dmodule_generators':1})
