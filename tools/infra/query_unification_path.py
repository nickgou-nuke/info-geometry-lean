#!/usr/bin/env python3
"""Query a typed dependency path inside one validated declaration generation.

This is a navigation tool over Lean's ``type`` / ``value`` dependency DAG. It
does not infer equivalence, representation, or analogy edges between lanes.
Both endpoint selectors must resolve uniquely in the selected immutable graph.
"""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Any

if __package__ in (None, ""):
    sys.path.insert(0, str(Path(__file__).resolve().parents[2]))

from tools.infra.arango_causal_memory import (  # noqa: E402
    ArangoCausalMemory,
    ArangoError,
    default_target,
)
from tools.infra.decl_graph_generation import (  # noqa: E402
    resolve_decl_graph_generation,
)


class _RestAql:
    """Adapt the maintained REST client to the generation validator interface."""

    def __init__(self, client: ArangoCausalMemory):
        self.client = client

    def execute(self, query: str, *, bind_vars: dict[str, Any] | None = None) -> list[Any]:
        return self.client.execute_aql(query, bind_vars).get("result", [])


class _RestCollection:
    def __init__(self, db: "_RestDatabase", name: str):
        self.db = db
        self.name = name

    def count(self) -> int:
        rows = self.db.aql.execute(
            "RETURN LENGTH(@@collection)", bind_vars={"@collection": self.name}
        )
        if len(rows) != 1 or not isinstance(rows[0], int):
            raise ArangoError(f"could not read count for collection {self.name!r}")
        return rows[0]


class _RestDatabase:
    def __init__(self, client: ArangoCausalMemory):
        self.client = client
        self.aql = _RestAql(client)

    def has_collection(self, name: str) -> bool:
        return self.client.collection_exists(name)

    def collection(self, name: str) -> _RestCollection:
        return _RestCollection(self, name)


def _resolve_anchor(
    client: ArangoCausalMemory,
    decl_collection: str,
    selector: str,
    label: str,
) -> dict[str, str]:
    rows = client.execute_aql(
        """
        LET exact = FIRST(
          FOR d IN @@decls
            FILTER d.name == @selector
            LIMIT 1
            RETURN d
        )
        LET matches = exact == null ? (
          FOR d IN @@decls
            FILTER CONTAINS(LOWER(d.name), LOWER(@selector))
            SORT d.name
            LIMIT 11
            RETURN d
        ) : [exact]
        RETURN matches[* RETURN {id: CURRENT._id, key: CURRENT._key, name: CURRENT.name}]
        """,
        {"@decls": decl_collection, "selector": selector},
    ).get("result", [])
    matches = rows[0] if len(rows) == 1 and isinstance(rows[0], list) else []
    if not matches:
        raise ValueError(f"{label} selector {selector!r} matched no declaration")
    if len(matches) != 1:
        choices = ", ".join(item.get("name", "<unnamed>") for item in matches[:10])
        suffix = ", …" if len(matches) > 10 else ""
        raise ValueError(
            f"{label} selector {selector!r} is ambiguous ({len(matches)}+ matches): "
            f"{choices}{suffix}; use an exact fully qualified declaration name"
        )
    anchor = matches[0]
    if not all(isinstance(anchor.get(field), str) and anchor[field] for field in ("id", "key", "name")):
        raise ValueError(f"{label} lookup returned an incomplete declaration record")
    return anchor


def find_path(
    client: ArangoCausalMemory,
    generation_id: str,
    source: str,
    target: str,
) -> dict[str, Any]:
    """Validate a generation and return a direction-preserving shortest path."""
    generation = resolve_decl_graph_generation(
        _RestDatabase(client), generation_id  # type: ignore[arg-type]
    )
    source_decl = _resolve_anchor(client, generation["declCollection"], source, "source")
    target_decl = _resolve_anchor(client, generation["declCollection"], target, "target")
    result: dict[str, Any] = {
        "generation": {
            "id": generation_id,
            "buildFingerprint": generation["buildFingerprint"],
            "importRoot": generation["importRoot"],
            "namespace": generation["namespace"],
            "declCollection": generation["declCollection"],
            "edgeCollection": generation["edgeCollection"],
        },
        "source": source_decl,
        "target": target_decl,
        "path": [],
    }
    if source_decl["id"] == target_decl["id"]:
        result["path"] = [{"declaration": source_decl, "via": None}]
        return result

    rows = client.execute_aql(
        """
        FOR v, e IN ANY SHORTEST_PATH @src TO @dst @@edges
          RETURN {
            declaration: {id: v._id, key: v._key, name: v.name, module: v.module},
            via: {
              from: e._from,
              to: e._to,
              kind: e.kind
            }
          }
        """,
        {
            "src": source_decl["id"],
            "dst": target_decl["id"],
            "@edges": generation["edgeCollection"],
        },
    ).get("result", [])
    # Arango includes the start vertex with a null edge in SHORTEST_PATH
    # results. The source is already prepended below, so remove that sentinel.
    rows = [
        row for row in rows
        if not (
            isinstance(row, dict)
            and isinstance(row.get("declaration"), dict)
            and row["declaration"].get("id") == source_decl["id"]
            and isinstance(row.get("via"), dict)
            and row["via"].get("from") is None
            and row["via"].get("to") is None
        )
    ]
    if not rows:
        raise ValueError(
            f"no type/value dependency path in generation {generation_id!r} "
            f"from {source_decl['name']} to {target_decl['name']}"
        )
    result["path"] = [{"declaration": source_decl, "via": None}, *rows]
    for previous, current in zip(result["path"], result["path"][1:]):
        previous_id = previous["declaration"].get("id")
        current_id = current.get("declaration", {}).get("id")
        via = current.get("via")
        edge_from = via.get("from") if isinstance(via, dict) else None
        edge_to = via.get("to") if isinstance(via, dict) else None
        if (
            not isinstance(previous_id, str)
            or not isinstance(current_id, str)
            or not isinstance(via, dict)
            or via.get("kind") not in ("type", "value")
            or not isinstance(edge_from, str)
            or not isinstance(edge_to, str)
            or not (
                (edge_from == previous_id and edge_to == current_id)
                or (edge_from == current_id and edge_to == previous_id)
            )
        ):
            raise ArangoError("shortest-path response contains a malformed dependency step")
    if result["path"][-1]["declaration"].get("id") != target_decl["id"]:
        raise ArangoError("shortest-path response did not terminate at the requested target")
    return result


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--generation-id", required=True,
                        help="Exact complete immutable declaration-graph generation")
    parser.add_argument("--source", required=True,
                        help="Exact declaration name or unique case-insensitive substring")
    parser.add_argument("--target", required=True,
                        help="Exact declaration name or unique case-insensitive substring")
    parser.add_argument("--output", type=Path,
                        help="Optional JSON output file; stdout remains the default")
    parser.add_argument("--endpoint", default=None)
    parser.add_argument("--database", default=None)
    parser.add_argument("--user", default=None)
    parser.add_argument("--password", default=None)
    args = parser.parse_args(argv)

    base = default_target()
    from tools.infra.arango_causal_memory import ArangoTarget
    client = ArangoCausalMemory(ArangoTarget(
        endpoint=(args.endpoint or base.endpoint).rstrip("/"),
        database=args.database or base.database,
        username=args.user if args.user is not None else base.username,
        password=args.password if args.password is not None else base.password,
    ))
    try:
        payload = find_path(client, args.generation_id, args.source, args.target)
    except (ArangoError, ValueError) as exc:
        print(f"query-unification-path: {exc}", file=sys.stderr)
        return 2

    rendered = json.dumps(payload, indent=2, ensure_ascii=False) + "\n"
    if args.output:
        args.output.write_text(rendered, encoding="utf-8")
    else:
        sys.stdout.write(rendered)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
