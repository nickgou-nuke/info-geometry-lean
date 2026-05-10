from __future__ import annotations

from tools.infra.arango_dag_algorithms import ArangoTarget, run_aql


def default_target() -> ArangoTarget:
    return ArangoTarget(
        endpoint="http://127.0.0.1:8530",
        username="root",
        password="alexandria_root",
        database="infogeometry",
    )


def main() -> int:
    query = """
FOR v IN raw_infotree_nodes
  FILTER v.decl_name LIKE "%Context%"
  RETURN v.decl_name
"""
    res = run_aql(default_target(), query)
    print("Nodes with Context in decl_name:")
    for name in res:
        print(name)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
