from arango import ArangoClient

client = ArangoClient(hosts='http://localhost:8529')
sys_db = client.db('_system', username='root', password='')

dbs = sys_db.databases()
for db_name in dbs:
    try:
        db = client.db(db_name, username='root', password='')
        for coll in db.collections():
            if coll['name'].startswith('_'): continue
            query = f'FOR doc IN {coll["name"]} FILTER doc.content LIKE "%exterior algebra%" OR doc.content LIKE "%submodule dimensions%" LIMIT 5 RETURN doc'
            try:
                cursor = db.aql.execute(query)
                for doc in cursor:
                    print(f"Match in DB {db_name}, Coll {coll['name']}: {str(doc)[:200]}")
            except Exception as e:
                pass
    except Exception as e:
        pass
