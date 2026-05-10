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
    query = "FOR v IN arango_dag_components FILTER v.representative != null LIMIT 10 RETURN v.representative"
    res = run_aql(default_target(), query)
    print("Representatives:", res)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
