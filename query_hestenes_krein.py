from arango import ArangoClient
client = ArangoClient(hosts='http://localhost:8540')
db = client.db('hive_memory', username='root', password='hive_brain')

aql = """
FOR doc IN Thoughts
  FILTER doc.content LIKE "%Hestenes%" OR doc.content LIKE "%Krein%"
  SORT doc.timestamp DESC
  LIMIT 5
  RETURN {
    type: doc.type,
    content: doc.content
  }
"""

cursor = db.aql.execute(aql)
for doc in cursor:
    print(f"[{doc['type']}]")
    print(doc['content'])
    print("-" * 40)
