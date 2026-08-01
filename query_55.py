from arango import ArangoClient
from pathlib import Path
from tools.infra.arango_env import (
    load_repo_arango_env,
    arango_endpoint,
    arango_username,
    arango_password,
    arango_database,
)

load_repo_arango_env(Path('.').resolve())
client = ArangoClient(hosts=arango_endpoint())
db = client.db(arango_database(), username=arango_username(), password=arango_password())

q = '''
FOR d IN decls
  FILTER d.name LIKE "%55%" OR d.name LIKE "%5_5%" OR d.name LIKE "%splitMetric10D%" OR d.name LIKE "%O55%"
  RETURN {name: d.name, kind: d.kind, module: d.module, attrs: d.attrs}
'''
print("=== 5,5 / 55 Declarations in DAG ===")
for doc in db.aql.execute(q):
    print(f'{doc["name"]} ({doc["kind"]}) - {doc["module"]}')
