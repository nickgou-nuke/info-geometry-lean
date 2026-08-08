from arango import ArangoClient

client = ArangoClient(hosts='http://localhost:8529')
db = client.db('agent_brain', username='root', password='')

query = """
FOR node IN lean_theorems
  FILTER node.status == "Generalized_Sorry" OR node.status == "Sorry"
  RETURN node
"""

try:
    cursor = db.aql.execute(query)
    results = list(cursor)
    print(f"Total Null Core (Generalized Sorry) Theorems: {len(results)}")
    for doc in results:
        print(f"Theorem: {doc['_key']}")
        print(f"File: {doc.get('file', 'N/A')}")
        print(f"Equation: {doc.get('equation', 'N/A')}")
        print("-" * 80)
except Exception as e:
    print(f"Error: {e}")
