from arango import ArangoClient
client = ArangoClient(hosts='http://localhost:8540')
db = client.db('hive_memory', username='root', password='hive_brain')

for collection in db.collections():
    if not collection['name'].startswith('_'):
        col = db.collection(collection['name'])
        print(f"Collection: {collection['name']}, count: {col.count()}")
