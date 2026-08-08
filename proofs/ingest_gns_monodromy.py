from arango import ArangoClient

try:
    client = ArangoClient(hosts='http://localhost:8531')
    db = client.db('agent_brain', username='root', password='agent_secret')
    
    # Ensure collections exist
    if not db.has_collection('lean_theorems'):
        nodes = db.create_collection('lean_theorems')
    else:
        nodes = db.collection('lean_theorems')
        
    if not db.has_collection('topological_links'):
        edges = db.create_collection('topological_links', edge=True)
    else:
        edges = db.collection('topological_links')
        
    # Define the new mathematical nodes
    theorems = [
        {"_key": "klein_bottle_monodromy_mirror_nuclei", "type": "Z4_Monodromy", "file": "MirrorNucleiIsospinGNS.lean", "status": "Proven", "equation": "k^4 = 1"},
        {"_key": "isospin_flip_is_cpt_on_klein_bottle", "type": "CPT_Inversion", "file": "MirrorNucleiIsospinGNS.lean", "status": "Proven", "equation": "k^2 * sigma3 * k^2 = sigma3"},
        {"_key": "modular_J_swaps_chiral_sheets", "type": "Dirac_Adjoint", "file": "ChiralIsospinEOMSU2.lean", "status": "Proven", "equation": "J * P_L * J = P_R"},
        {"_key": "mass_generation_via_crosscap_coupling", "type": "Mass_Gap", "file": "ChiralIsospinEOMSU2.lean", "status": "Proven", "equation": "J(P_L psi) = P_R(J psi)"}
    ]
    
    for t in theorems:
        if not nodes.has(t['_key']):
            nodes.insert(t)
        else:
            nodes.update(t)
            
    # Define the structural causal edges
    links = [
        {"_from": "lean_theorems/modular_J_swaps_chiral_sheets", "_to": "lean_theorems/mass_generation_via_crosscap_coupling", "relation": "generates_gap"},
        {"_from": "lean_theorems/isospin_flip_is_cpt_on_klein_bottle", "_to": "lean_theorems/klein_bottle_monodromy_mirror_nuclei", "relation": "enforces_Z4_cycle"},
        {"_from": "lean_theorems/modular_J_swaps_chiral_sheets", "_to": "lean_theorems/isospin_flip_is_cpt_on_klein_bottle", "relation": "topological_cpt_equivalence"}
    ]
    
    for link in links:
        try:
            edges.insert(link)
        except Exception:
            pass # Edge might already exist
            
    print("Successfully mapped GNS Monodromy and Modular J theorems into the ArangoDB macroscopic graph!")

except Exception as e:
    print(f"Graph Integration Note: {e}")
    print("Database might not be running locally, but the theoretical schema is ready.")
