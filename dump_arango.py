import json
from arango import ArangoClient
client = ArangoClient(hosts='http://localhost:8540')
db = client.db('hive_memory', username='root', password='hive_brain')

with open("arango_dump.txt", "w") as f:
    cursor = db.aql.execute("FOR doc IN Thoughts RETURN doc")
    for doc in cursor:
        f.write(json.dumps(doc) + "\n")
