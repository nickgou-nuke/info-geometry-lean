#!/usr/bin/env python3
"""Read-only cross-concept search over the compiler-backed declaration DAG.

The command finds bounded shared prerequisites between two declaration-name
patterns.  It is navigation evidence only: source owners and Lean proofs are
the authority for any semantic bridge.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import sys
from pathlib import Path
from typing import Any

if __package__ in (None, ""):
    sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
    from tools.infra.arango_causal_memory import (  # type: ignore
        ArangoCausalMemory,
        ArangoError,
        default_target,
    )
else:
    from .arango_causal_memory import ArangoCausalMemory, ArangoError, default_target


DEFAULT_QUANTUM = ("tomita", "kms")
DEFAULT_CLASSICAL = ("fisher", "onsager")


def _positive(value: str, name: str) -> int:
    try:
        parsed = int(value)
    except ValueError as exc:
        raise argparse.ArgumentTypeError(f"{name} must be an integer") from exc
    if parsed < 1:
        raise argparse.ArgumentTypeError(f"{name} must be positive")
    return parsed


def _pattern(terms: tuple[str, ...]) -> str:
    escaped = [re.escape(term.strip().lower()) for term in terms if term.strip()]
    if not escaped:
        raise ValueError("at least one non-empty concept term is required")
    return "|".join(escaped)


def build_query() -> str:
    return """
LET quantum = (
  FOR d IN @@decl_collection
    FILTER REGEX_TEST(LOWER(d.name), @quantum_pattern)
    SORT d.name
    LIMIT @seed_limit
    RETURN d
)
LET classical = (
  FOR d IN @@decl_collection
    FILTER REGEX_TEST(LOWER(d.name), @classical_pattern)
    SORT d.name
    LIMIT @seed_limit
    RETURN d
)
FOR q IN quantum
  LET qdeps = (
    FOR v, e, p IN 1..@depth OUTBOUND q @@edge_collection
      OPTIONS {bfs: true, uniqueVertices: "global"}
      LIMIT @cone_limit
      RETURN v._id
  )
  FOR c IN classical
    LET cdeps = (
      FOR v, e, p IN 1..@depth OUTBOUND c @@edge_collection
        OPTIONS {bfs: true, uniqueVertices: "global"}
        LIMIT @cone_limit
        RETURN v._id
    )
    LET shared = INTERSECTION(qdeps, cdeps)
    FILTER LENGTH(shared) > 0
    LIMIT @pair_limit
    RETURN {
      quantum: {id: q._id, name: q.name, kind: q.kind,
                module: q.module, file: q.file, line: q.line},
      classical: {id: c._id, name: c.name, kind: c.kind,
                  module: c.module, file: c.file, line: c.line},
      sharedCount: LENGTH(shared),
      sharedNodes: (
        FOR d IN @@decl_collection
          FILTER d._id IN shared
          SORT d.name
          LIMIT @shared_limit
          RETURN {id: d._id, name: d.name, kind: d.kind,
                  module: d.module, file: d.file, line: d.line}
      )
    }
""".strip()


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Find bounded shared declaration-DAG prerequisites read-only."
    )
    parser.add_argument("--quantum-term", action="append", dest="quantum_terms")
    parser.add_argument("--classical-term", action="append", dest="classical_terms")
    parser.add_argument("--depth", type=lambda v: _positive(v, "--depth"), default=3)
    parser.add_argument("--seed-limit", type=lambda v: _positive(v, "--seed-limit"), default=20)
    parser.add_argument("--cone-limit", type=lambda v: _positive(v, "--cone-limit"), default=200)
    parser.add_argument("--pair-limit", type=lambda v: _positive(v, "--pair-limit"), default=200)
    parser.add_argument("--shared-limit", type=lambda v: _positive(v, "--shared-limit"), default=50)
    parser.add_argument("--decl-collection", default="decls")
    parser.add_argument("--edge-collection", default="edges")
    parser.add_argument("--json-out", type=Path)
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    quantum = tuple(args.quantum_terms or DEFAULT_QUANTUM)
    classical = tuple(args.classical_terms or DEFAULT_CLASSICAL)
    query = build_query()
    bind_vars: dict[str, Any] = {
        "@decl_collection": args.decl_collection,
        "@edge_collection": args.edge_collection,
        "quantum_pattern": _pattern(quantum),
        "classical_pattern": _pattern(classical),
        "depth": args.depth,
        "seed_limit": args.seed_limit,
        "cone_limit": args.cone_limit,
        "pair_limit": args.pair_limit,
        "shared_limit": args.shared_limit,
    }
    try:
        target = default_target()
        response = ArangoCausalMemory(target).execute_aql(
            query, bind_vars, allow_write=False, batch_size=args.pair_limit
        )
    except (ArangoError, ValueError) as exc:
        print(f"astaql-concept-bridge: {exc}", file=sys.stderr)
        return 2

    payload = {
        "authority": "compiler_backed_decls_edges",
        "readOnly": True,
        "endpoint": target.endpoint,
        "database": target.database,
        "declCollection": args.decl_collection,
        "edgeCollection": args.edge_collection,
        "quantumTerms": list(quantum),
        "classicalTerms": list(classical),
        "bounds": {
            "depth": args.depth,
            "seedLimit": args.seed_limit,
            "coneLimit": args.cone_limit,
            "pairLimit": args.pair_limit,
            "sharedLimit": args.shared_limit,
        },
        "querySha256": hashlib.sha256(query.encode("utf-8")).hexdigest(),
        "result": response.get("result", []),
        "stats": response.get("extra", {}).get("stats", {}),
        "semanticWarning": (
            "Shared graph prerequisites are navigation evidence; inspect owner "
            "source and prove any claimed semantic comparison in Lean."
        ),
    }
    rendered = json.dumps(payload, ensure_ascii=False, indent=2)
    if args.json_out:
        args.json_out.write_text(rendered + "\n", encoding="utf-8")
    else:
        print(rendered)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
