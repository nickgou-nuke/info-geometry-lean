import sys
from tools.infra.arango_dag_algorithms import run_aql, ArangoTarget

target = ArangoTarget(
    endpoint="http://127.0.0.1:8530",
    username="root",
    password="alexandria_root",
    database="infogeometry"
)

query = "FOR v IN arango_dag_components FILTER v.representative != null LIMIT 10 RETURN v.representative"
res = run_aql(target, query)
print("Representatives:", res)
