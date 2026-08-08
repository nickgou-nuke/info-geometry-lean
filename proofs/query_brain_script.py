from arango import ArangoClient

client = ArangoClient(hosts='http://localhost:8531')
db = client.db('agent_brain', username='root', password='agent_secret')

query = """
FOR step IN steps
  FILTER step.content LIKE "%DeterminantLineBundle%"
  RETURN step
"""

cursor = db.aql.execute(query)
for doc in cursor:
    print(f"[{doc['conversation_id']} - Step {doc['step_index']}] {doc['type']}: {doc['content'][:1000]}...")
