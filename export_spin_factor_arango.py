import json
from arango import ArangoClient
import datetime

def main():
    print("Connecting to ArangoDB Hive Memory...")
    client = ArangoClient(hosts='http://localhost:8540')
    db = client.db('hive_memory', username='root', password='hive_brain')
    
    thoughts = db.collection('Thoughts')
    causal_links = db.collection('CausalLinks')
    
    timestamp = datetime.datetime.now().isoformat()
    
    # Define the AST nodes to inject
    nodes = [
        {
            '_key': 'module_spinfactorembedding',
            'type': 'MODULE',
            'name': 'InfoGeometry.Canonical.SpinFactorEmbedding',
            'description': 'Bridge embedding the H2(O\') Jordan Spin Factor into the 10D O(5,5) gauge space.',
            'timestamp': timestamp,
            'status': 'VERIFIED'
        },
        {
            '_key': 'def_spinfactortovector10d',
            'type': 'DEFINITION',
            'name': 'spinFactorToVector10D',
            'lean_type': 'JordanMatrix2 → (Fin 10 → ℝ)',
            'description': 'Canonical linear isomorphism Φ projecting the expert state to 10D.',
            'timestamp': timestamp,
            'status': 'VERIFIED'
        },
        {
            '_key': 'thm_spinfactordeteqsplitmetric',
            'type': 'THEOREM',
            'name': 'spinFactor_det_eq_splitMetric',
            'description': 'Proof that det(X) equals the quadratic form Φ(X)ᵀ η Φ(X).',
            'timestamp': timestamp,
            'status': 'VERIFIED',
            'sorries': 0
        },
        {
            '_key': 'thm_o55preservesspinfactordet',
            'type': 'THEOREM',
            'name': 'transpose_o55_preserves_spin_factor_determinant',
            'description': 'Proof that the O(5,5) gauge group transformations strictly preserve the KAN Radon-Nikodym Entropy (the determinant).',
            'timestamp': timestamp,
            'status': 'VERIFIED',
            'sorries': 0
        }
    ]
    
    for node in nodes:
        if not thoughts.has(node['_key']):
            thoughts.insert(node)
            print(f"Inserted node: {node['_key']}")
        else:
            thoughts.update(node)
            print(f"Updated node: {node['_key']}")
            
    # Define causal links (edges)
    edges = [
        {'_from': 'Thoughts/module_spinfactorembedding', '_to': 'Thoughts/def_spinfactortovector10d', 'relation': 'CONTAINS'},
        {'_from': 'Thoughts/module_spinfactorembedding', '_to': 'Thoughts/thm_spinfactordeteqsplitmetric', 'relation': 'CONTAINS'},
        {'_from': 'Thoughts/module_spinfactorembedding', '_to': 'Thoughts/thm_o55preservesspinfactordet', 'relation': 'CONTAINS'},
        {'_from': 'Thoughts/def_spinfactortovector10d', '_to': 'Thoughts/thm_spinfactordeteqsplitmetric', 'relation': 'USED_IN'},
        {'_from': 'Thoughts/def_spinfactortovector10d', '_to': 'Thoughts/thm_o55preservesspinfactordet', 'relation': 'USED_IN'}
    ]
    
    for edge in edges:
        # Check if edge exists using AQL
        cursor = db.aql.execute(
            "FOR e IN CausalLinks FILTER e._from == @frm AND e._to == @to RETURN e",
            bind_vars={'frm': edge['_from'], 'to': edge['_to']}
        )
        if cursor.empty():
            causal_links.insert(edge)
            print(f"Inserted edge from {edge['_from']} to {edge['_to']}")
        else:
            print(f"Edge from {edge['_from']} to {edge['_to']} already exists")
            
    print("ASTAQLHASH synchronization complete!")

if __name__ == "__main__":
    main()
