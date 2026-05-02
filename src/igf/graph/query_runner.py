from __future__ import annotations

from typing import Any

from .query_registry import get_query


def run_query(db: Any, query_id: str, **bind_vars: Any) -> list[Any]:
    query = get_query(query_id)
    return list(db.aql.execute(query.aql, bind_vars=bind_vars))


def resolve_run_id(db: Any, run_id: str | None) -> str:
    if run_id:
        return run_id
    rows = run_query(db, "verify.latest_run_id")
    if not rows or not rows[0]:
        raise RuntimeError("No ig_patch_runs.run_id value found for latest run resolution")
    return str(rows[0])

