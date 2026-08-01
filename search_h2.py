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
  FILTER d.name LIKE "%H2%" OR d.name LIKE "%SpinFactor%" OR d.name LIKE "%JordanSpin%"
  RETURN {name: d.name, module: d.module}
'''
for r in db.aql.execute(q):
    print(f'{r["name"]} - {r["module"]}')
