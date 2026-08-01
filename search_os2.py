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
  FILTER d.module LIKE "%Jordan%" OR d.module LIKE "%SplitOctonion%" OR d.name LIKE "%H2%"
  COLLECT mod = d.module WITH COUNT INTO c
  SORT c DESC
  RETURN {module: mod, count: c}
'''
for r in db.aql.execute(q):
    print(r)
