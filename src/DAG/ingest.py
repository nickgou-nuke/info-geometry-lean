import json
import mgclient

def ingest(host="127.0.0.1", port=7687):
    conn = mgclient.connect(host=host, port=port)
    cursor = conn.cursor()

    # Clear existing data for a fresh start
    print("Clearing existing graph...")
    cursor.execute("MATCH (n) DETACH DELETE n;")
    
    # Indices for speed
    print("Creating indices...")
    cursor.execute("CREATE INDEX ON :Expr(id);")
    cursor.execute("CREATE INDEX ON :Declaration(id);")
    conn.commit()

    # Helper function to batch load JSONL
    def load_jsonl(filename):
        with open(filename, 'r') as f:
            for line in f:
                yield json.loads(line)

    def batch(iterable, n=1):
        l = len(iterable)
        for ndx in range(0, l, n):
            yield iterable[ndx:min(ndx + n, l)]

    # 1. Load Expr Nodes
    print("Ingesting Expr nodes...")
    all_nodes = list(load_jsonl('nodes.jsonl'))
    for b in batch(all_nodes, 1000):
        query = "UNWIND $batch AS n CREATE (:Expr {id: n.id, kind: n.kind, info: toString(n.info)});"
        cursor.execute(query, {'batch': b})
    conn.commit()

    # 2. Load Declaration Nodes
    print("Ingesting Declaration nodes...")
    all_decls = list(load_jsonl('decls.jsonl'))
    for b in batch(all_decls, 500):
        query = "UNWIND $batch AS d CREATE (:Declaration {id: d.id, name: d.name, module: d.module});"
        cursor.execute(query, {'batch': b})
    conn.commit()

    # 3. Load Expr-to-Expr Edges
    print("Ingesting internal Expr edges...")
    all_edges = list(load_jsonl('edges.jsonl'))
    for b in batch(all_edges, 1000):
        query = """
        UNWIND $batch AS e
        MATCH (src:Expr {id: e.source}), (tgt:Expr {id: e.target})
        CALL mg.create.relationship(src, tgt, e.role) YIELD rel
        RETURN count(rel);
        """
        cursor.execute(query, {'batch': b})
    conn.commit()

    # 4. Load Declaration-to-Expr Edges
    print("Ingesting Declaration-to-Expr edges...")
    all_decl_edges = list(load_jsonl('decl_edges.jsonl'))
    for b in batch(all_decl_edges, 500):
        query = """
        UNWIND $batch AS e
        MATCH (src:Declaration {id: e.source}), (tgt:Expr {id: e.target})
        CALL mg.create.relationship(src, tgt, e.role) YIELD rel
        RETURN count(rel);
        """
        cursor.execute(query, {'batch': b})
    conn.commit()

    print("Ingestion complete!")
    conn.close()

if __name__ == "__main__":
    ingest()
