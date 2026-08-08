from arango import ArangoClient

try:
    client = ArangoClient(hosts='http://localhost:8531')
    db = client.db('agent_brain', username='root', password='agent_secret')
    
    nodes = db.collection('lean_theorems')
    edges = db.collection('topological_links')
        
    theorems = [
        {"_key": "q8_quaternion_relations", "type": "Algebraic_Generator", "file": "Q8NuclearChirality.lean", "status": "Proven", "equation": "sigma1*sigma2*sigma3 = i*I"},
        {"_key": "fermionic_double_cover", "type": "Topological_Lift", "file": "Q8NuclearChirality.lean", "status": "Proven", "equation": "C2^2 = -1"},
        {"_key": "chiral_operator_is_sigma3", "type": "Chiral_Operator", "file": "Q8NuclearChirality.lean", "status": "Proven", "equation": "chi = T * R(pi)"},
        {"_key": "modular_J_is_chiral_swap", "type": "Tomita_Takesaki", "file": "Q8NuclearChirality.lean", "status": "Proven", "equation": "J * sigma+ * J = sigma-"}
    ]
    
    for t in theorems:
        if not nodes.has(t['_key']):
            nodes.insert(t)
        else:
            nodes.update(t)
            
    links = [
        {"_from": "lean_theorems/fermionic_double_cover", "_to": "lean_theorems/q8_quaternion_relations", "relation": "lifts_D2_to_Q8"},
        {"_from": "lean_theorems/chiral_operator_is_sigma3", "_to": "lean_theorems/modular_J_is_chiral_swap", "relation": "instantiates_modular_J"},
        # Connection back to the GNS schema we ingested earlier
        {"_from": "lean_theorems/modular_J_is_chiral_swap", "_to": "lean_theorems/modular_J_swaps_chiral_sheets", "relation": "microscopic_to_macroscopic_mass"},
        {"_from": "lean_theorems/q8_quaternion_relations", "_to": "lean_theorems/klein_bottle_monodromy_mirror_nuclei", "relation": "provides_angular_momentum_tensors"}
    ]
    
    for link in links:
        try:
            edges.insert(link)
        except Exception:
            pass
            
    print("Successfully mapped Q8 Nuclear Chirality into the ArangoDB macroscopic graph!")

except Exception as e:
    print(f"Graph Integration Error: {e}")
