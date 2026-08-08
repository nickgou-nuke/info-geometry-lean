from arango import ArangoClient

client = ArangoClient(hosts='http://localhost:8530')
db = client.db('agent_brain', username='root', password='alexandria_root')

query = """
FOR step IN steps
  FILTER step.content LIKE "%superallowed%"
  FILTER step.conversation_id != "2cf6aa34-86b3-4572-831b-dc25dc081fa3"
  RETURN step
"""

cursor = db.aql.execute(query)
for doc in cursor:
    print(f"[{doc.get('conversation_id')} - Step {doc.get('step_index')}] {doc.get('type')}:\n{doc.get('content')}\n---")
