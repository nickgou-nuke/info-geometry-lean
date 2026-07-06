from arango import ArangoClient
client = ArangoClient(hosts='http://localhost:8540')
db = client.db('hive_memory', username='root', password='hive_brain')

aql = """
FOR doc IN Thoughts
  FILTER doc.content_preview LIKE "%Hestenes%" OR doc.content_preview LIKE "%Krein%"
         OR doc.code_extracted LIKE "%Hestenes%" OR doc.code_extracted LIKE "%Krein%"
  SORT doc.timestamp DESC
  LIMIT 5
  RETURN {
    type: doc.type,
    preview: doc.content_preview,
    code: doc.code_extracted
  }
"""

cursor = db.aql.execute(aql)
for doc in cursor:
    print(f"[{doc['type']}]")
    print(doc['preview'])
    print(doc['code'][:300] if doc['code'] else "None")
    print("-" * 40)
