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

# Search for anything related to H2, SplitOctonion, Os, Jordan, or O55
q = '''
FOR d IN decls
  FILTER d.name LIKE "%SplitOctonion%" OR d.name LIKE "%H2%" OR d.name LIKE "%Jordan%" OR d.name LIKE "%Cayley%" OR d.name LIKE "%OsQ%" OR d.name LIKE "%SplitGauge%"
  RETURN {name: d.name, kind: d.kind, module: d.module}
'''
results = list(db.aql.execute(q))
print(f"=== Found {len(results)} declarations ===")
for r in results[:100]:  # Limit output just in case
    print(f'{r["name"]} ({r["kind"]}) - {r["module"]}')
