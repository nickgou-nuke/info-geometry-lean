from arango import ArangoClient
import json

client = ArangoClient(hosts='http://localhost:8531')
db = client.db('agent_brain', username='root', password='agent_secret')

query = """
FOR step IN steps
  FILTER step.content LIKE "%equivalence class%" AND step.content LIKE "%sorry%"
  SORT step.step_index DESC
  LIMIT 5
  RETURN step.content
"""

cursor = db.aql.execute(query)
for doc in cursor:
    print("--- RESULT ---")
    print(doc[:500])
