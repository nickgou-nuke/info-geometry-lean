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
LET quantumMatchedCount = LENGTH(
  FOR d IN @@decl_collection
    FILTER (LENGTH(@quantum_names) > 0 AND d.name IN @quantum_names) OR
      (LENGTH(@quantum_names) == 0 AND
        REGEX_TEST(LOWER(d.name), @quantum_pattern))
    FILTER @quantum_module_prefix == "" OR
      STARTS_WITH(LOWER(d.module), LOWER(@quantum_module_prefix))
    RETURN 1
)
LET classicalMatchedCount = LENGTH(
  FOR d IN @@decl_collection
    FILTER (LENGTH(@classical_names) > 0 AND d.name IN @classical_names) OR
      (LENGTH(@classical_names) == 0 AND
        REGEX_TEST(LOWER(d.name), @classical_pattern))
    FILTER @classical_module_prefix == "" OR
      STARTS_WITH(LOWER(d.module), LOWER(@classical_module_prefix))
    RETURN 1
)
LET quantum = (
  FOR d IN @@decl_collection
    FILTER (LENGTH(@quantum_names) > 0 AND d.name IN @quantum_names) OR
      (LENGTH(@quantum_names) == 0 AND
        REGEX_TEST(LOWER(d.name), @quantum_pattern))
    FILTER @quantum_module_prefix == "" OR
      STARTS_WITH(LOWER(d.module), LOWER(@quantum_module_prefix))
    SORT d.module, d.name
    LIMIT @seed_limit
    RETURN d
)
LET classical = (
  FOR d IN @@decl_collection
    FILTER (LENGTH(@classical_names) > 0 AND d.name IN @classical_names) OR
      (LENGTH(@classical_names) == 0 AND
        REGEX_TEST(LOWER(d.name), @classical_pattern))
    FILTER @classical_module_prefix == "" OR
      STARTS_WITH(LOWER(d.module), LOWER(@classical_module_prefix))
    SORT d.module, d.name
    LIMIT @seed_limit
    RETURN d
)
LET matches = (
  FOR q IN quantum
    LET qdeps = (
      FOR v, e, p IN 1..@depth OUTBOUND q._id @@edge_collection
        PRUNE e.kind NOT IN ["type", "value"]
        OPTIONS {bfs: true, uniqueVertices: "global"}
        FILTER e.kind IN ["type", "value"]
        LIMIT @cone_limit
        RETURN {id: v._id, depth: LENGTH(p.edges),
                path: p.vertices[*]._id, edgeKinds: p.edges[*].kind}
    )
    FOR c IN classical
      LET cdeps = (
        FOR v, e, p IN 1..@depth OUTBOUND c._id @@edge_collection
          PRUNE e.kind NOT IN ["type", "value"]
          OPTIONS {bfs: true, uniqueVertices: "global"}
          FILTER e.kind IN ["type", "value"]
          LIMIT @cone_limit
          RETURN {id: v._id, depth: LENGTH(p.edges),
                  path: p.vertices[*]._id, edgeKinds: p.edges[*].kind}
      )
      LET quantumToClassicalPaths = (
        FOR v, e, p IN 1..@depth OUTBOUND q._id @@edge_collection
          PRUNE e.kind NOT IN ["type", "value"]
          OPTIONS {bfs: true, uniqueVertices: "path"}
          FILTER e.kind IN ["type", "value"] AND v._id == c._id
          LIMIT 1
          RETURN {path: p.vertices[*]._id, edgeIds: p.edges[*]._id,
                  edgeKinds: p.edges[*].kind}
      )
      LET classicalToQuantumPaths = (
        FOR v, e, p IN 1..@depth OUTBOUND c._id @@edge_collection
          PRUNE e.kind NOT IN ["type", "value"]
          OPTIONS {bfs: true, uniqueVertices: "path"}
          FILTER e.kind IN ["type", "value"] AND v._id == q._id
          LIMIT 1
          RETURN {path: p.vertices[*]._id, edgeIds: p.edges[*]._id,
                  edgeKinds: p.edges[*].kind}
      )
      LET shared = INTERSECTION(qdeps[*].id, cdeps[*].id)
      FILTER LENGTH(shared) > 0 OR LENGTH(quantumToClassicalPaths) > 0 OR
        LENGTH(classicalToQuantumPaths) > 0
      LIMIT @pair_limit
      RETURN {
        quantum: {id: q._id, name: q.name, kind: q.kind,
                  module: q.module, file: q.file, line: q.line,
                  dagShapeHash: q.dagShapeHash,
                  typeShapeHash: q.typeFingerprint.shapeHash,
                  valueAlgorithmVersion: q.valueFingerprint == null ? null :
                    q.valueFingerprint.algorithmVersion,
                  canonicalValueHash: q.canonicalValueHash},
        classical: {id: c._id, name: c.name, kind: c.kind,
                    module: c.module, file: c.file, line: c.line,
                    dagShapeHash: c.dagShapeHash,
                    typeShapeHash: c.typeFingerprint.shapeHash,
                    valueAlgorithmVersion: c.valueFingerprint == null ? null :
                      c.valueFingerprint.algorithmVersion,
                    canonicalValueHash: c.canonicalValueHash},
        sharedCount: LENGTH(shared),
        quantumToClassicalPaths: quantumToClassicalPaths,
        classicalToQuantumPaths: classicalToQuantumPaths,
        sharedNodes: (
          FOR id IN shared
            LET d = DOCUMENT(id)
            LET qpath = FIRST(FOR dep IN qdeps FILTER dep.id == id RETURN dep)
            LET cpath = FIRST(FOR dep IN cdeps FILTER dep.id == id RETURN dep)
            SORT d.name
            LIMIT @shared_limit
            RETURN {
              id: d._id, name: d.name, kind: d.kind, module: d.module,
              file: d.file, line: d.line, dagShapeHash: d.dagShapeHash,
              typeShapeHash: d.typeFingerprint.shapeHash,
              valueAlgorithmVersion: d.valueFingerprint == null ? null :
                d.valueFingerprint.algorithmVersion,
              canonicalValueHash: d.canonicalValueHash,
              quantumPath: qpath.path, quantumEdgeKinds: qpath.edgeKinds,
              classicalPath: cpath.path, classicalEdgeKinds: cpath.edgeKinds
            }
        )
      }
)
RETURN {
  quantumMatchedCount: quantumMatchedCount,
  classicalMatchedCount: classicalMatchedCount,
  quantumSelected: quantum[* RETURN {
    id: CURRENT._id, name: CURRENT.name, module: CURRENT.module,
    dagShapeHash: CURRENT.dagShapeHash,
    typeShapeHash: CURRENT.typeFingerprint.shapeHash,
    valueAlgorithmVersion: CURRENT.valueFingerprint == null ? null :
      CURRENT.valueFingerprint.algorithmVersion,
    canonicalValueHash: CURRENT.canonicalValueHash
  }],
  classicalSelected: classical[* RETURN {
    id: CURRENT._id, name: CURRENT.name, module: CURRENT.module,
    dagShapeHash: CURRENT.dagShapeHash,
    typeShapeHash: CURRENT.typeFingerprint.shapeHash,
    valueAlgorithmVersion: CURRENT.valueFingerprint == null ? null :
      CURRENT.valueFingerprint.algorithmVersion,
    canonicalValueHash: CURRENT.canonicalValueHash
  }],
  matches: matches
}
""".strip()


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Find bounded shared declaration-DAG prerequisites read-only."
    )
    parser.add_argument("--quantum-term", action="append", dest="quantum_terms")
    parser.add_argument("--classical-term", action="append", dest="classical_terms")
    parser.add_argument("--quantum-name", action="append", dest="quantum_names")
    parser.add_argument("--classical-name", action="append", dest="classical_names")
    parser.add_argument("--quantum-module-prefix", default="")
    parser.add_argument("--classical-module-prefix", default="")
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
    quantum_names = tuple(args.quantum_names or ())
    classical_names = tuple(args.classical_names or ())
    query = build_query()
    bind_vars: dict[str, Any] = {
        "@decl_collection": args.decl_collection,
        "@edge_collection": args.edge_collection,
        "quantum_pattern": _pattern(quantum),
        "classical_pattern": _pattern(classical),
        "quantum_names": list(quantum_names),
        "classical_names": list(classical_names),
        "quantum_module_prefix": args.quantum_module_prefix,
        "classical_module_prefix": args.classical_module_prefix,
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

    query_summary = next(iter(response.get("result", [])), {})
    matched_quantum = query_summary.get("quantumMatchedCount", 0)
    matched_classical = query_summary.get("classicalMatchedCount", 0)
    payload = {
        "authority": "compiler_backed_decls_edges",
        "readOnly": True,
        "endpoint": target.endpoint,
        "database": target.database,
        "declCollection": args.decl_collection,
        "edgeCollection": args.edge_collection,
        "quantumTerms": list(quantum),
        "classicalTerms": list(classical),
        "quantumNames": list(quantum_names),
        "classicalNames": list(classical_names),
        "modulePrefixes": {
            "quantum": args.quantum_module_prefix,
            "classical": args.classical_module_prefix,
        },
        "bounds": {
            "depth": args.depth,
            "seedLimit": args.seed_limit,
            "coneLimit": args.cone_limit,
            "pairLimit": args.pair_limit,
            "sharedLimit": args.shared_limit,
        },
        "querySha256": hashlib.sha256(query.encode("utf-8")).hexdigest(),
        "diagnostics": {
            "quantumMatchedCount": matched_quantum,
            "classicalMatchedCount": matched_classical,
            "quantumSelected": query_summary.get("quantumSelected", []),
            "classicalSelected": query_summary.get("classicalSelected", []),
            "emptyResultInterpretation": (
                "No declarations matched the filters."
                if matched_quantum == 0 or matched_classical == 0
                else "No direct dependency path or shared type/value prerequisite was found within the configured bounds."
            ) if not query_summary.get("matches") else None,
        },
        "result": query_summary.get("matches", []),
        "stats": response.get("extra", {}).get("stats", {}),
        "semanticWarning": (
            "Paths list compiler dependency edges only (type/value). Direct "
            "dependency paths, shared prerequisites, and structural hashes are "
            "navigation evidence; they do not prove semantic relations or graph "
            "completeness. Inspect owner "
            "source and prove any claimed bridge in Lean."
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
