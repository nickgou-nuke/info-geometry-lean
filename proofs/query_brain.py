from arango import ArangoClient
import json

try:
    client = ArangoClient(hosts='http://localhost:8529')
    db = client.db('agent_brain', username='root', password='')
    query = """
    FOR doc IN lean_theorems
      FILTER doc.name LIKE "%jarlskog%" OR doc.name LIKE "%cpPhase%" OR doc.name LIKE "%d2Square%" OR doc.name LIKE "%CKM%" OR doc.content LIKE "%jarlskog%"
      RETURN doc
    """
    cursor = db.aql.execute(query)
    for doc in cursor:
        print("-------")
        print(doc.get('name', 'no name'), doc.get('content', '')[:200])
except Exception as e:
    print(e)
