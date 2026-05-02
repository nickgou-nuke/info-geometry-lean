import sys
from tools.infra.arango_dag_algorithms import run_aql, ArangoTarget

target = ArangoTarget(
    endpoint="http://127.0.0.1:8530",
    username="root",
    password="alexandria_root",
    database="infogeometry"
)

query1 = """
FOR v IN raw_infotree_nodes
  FILTER v.decl_name LIKE "%Context%"
  RETURN v.decl_name
"""
res1 = run_aql(target, query1)
print("Nodes with Context in decl_name:")
for name in res1:
    print(name)
