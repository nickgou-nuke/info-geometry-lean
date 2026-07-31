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

print("=== Search for Triality ===")
q = '''
FOR d IN decls
  FILTER d.name LIKE "%Triality%"
  RETURN {name: d.name, module: d.module, kind: d.kind}
'''
results = list(db.aql.execute(q))
print(f"Found {len(results)} results. First 50:")
for r in results[:50]:
    print(f"{r['name']} ({r['kind']}) in {r['module']}")
