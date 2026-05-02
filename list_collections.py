import sys
from tools.infra.arango_dag_algorithms import run_aql, ArangoTarget

target = ArangoTarget(
    endpoint="http://127.0.0.1:8530",
    username="root",
    password="alexandria_root",
    database="infogeometry"
)

query = "RETURN COLLECTIONS()"
try:
    res = run_aql(target, query)
    print("Collections:", res)
except Exception as e:
    print(f"Error: {e}")
