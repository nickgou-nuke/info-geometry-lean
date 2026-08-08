from arango import ArangoClient
client = ArangoClient(hosts='http://localhost:8530')
sys_db = client.db('_system', username='root', password='alexandria_root')
print(sys_db.databases())
