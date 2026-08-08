from arango import ArangoClient

client = ArangoClient(hosts='http://localhost:8531')
db = client.db('agent_brain', username='root', password='agent_secret')

query = """
FOR step IN steps
  FILTER LOWER(step.content) LIKE "%methodology%" OR LOWER(step.content) LIKE "%ifortree%" OR LOWER(step.content) LIKE "%ast aql hash%"
  SORT step.step_index DESC
  LIMIT 10
  RETURN { idx: step.step_index, content: SUBSTRING(step.content, 0, 500) }
"""

try:
    cursor = db.aql.execute(query)
    found = False
    for doc in cursor:
        found = True
        print("FOUND:", doc['idx'])
        print(doc['content'])
        print("-" * 80)
    if not found:
        print("Nothing found.")
except Exception as e:
    print(f"Error: {e}")
