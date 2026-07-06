from arango import ArangoClient
client = ArangoClient(hosts='http://localhost:8540')
db = client.db('hive_memory', username='root', password='hive_brain')

aql = """
FOR doc IN Thoughts
  SORT doc.timestamp DESC
  LIMIT 1
  RETURN doc
"""
cursor = db.aql.execute(aql)
for doc in cursor:
    print(doc.keys())
