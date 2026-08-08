import json
from arango import ArangoClient

def dump():
    client = ArangoClient(hosts="http://localhost:8529")
    db = client.db("LeanAST", username="root", password="")
    
    v_coll = db.collection("Theorems")
    e_coll = db.collection("ProofSteps")
    
    nodes = []
    edges = []
    
    for v in v_coll.all():
        # ForceGraph needs id for nodes
        v['id'] = v['_id']
        nodes.append(v)
        
    for e in e_coll.all():
        # ForceGraph needs source and target
        e['source'] = e['_from']
        e['target'] = e['_to']
        edges.append(e)
        
    data = {
        "nodes": nodes,
        "links": edges
    }
    
    with open("/home/goutev/auto/ui/public/graph.json", "w") as f:
        json.dump(data, f)
        
    print(f"Dumped {len(nodes)} nodes and {len(edges)} links to public/graph.json")

if __name__ == "__main__":
    dump()
