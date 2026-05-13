#!/usr/bin/env python3
"""Ingest derived dual wire/gate topology into ArangoDB.

This imports the projection emitted by ``tools/infra/wire_topology_transform.py``:

* ``ig_wires.jsonl``
* ``ig_gates.jsonl``
* ``ig_wire_edges.jsonl``
* ``ig_scc.jsonl``
* ``ig_scc_edges.jsonl``
* ``ig_decl_topologies.jsonl``
* ``ig_hashes.jsonl``
* ``ig_logic_tokens.jsonl``
* ``ig_logic_vectors.jsonl``
* ``ig_text_index_docs.jsonl``
* ``ig_translation_candidates.jsonl``
* ``ig_translation_edges.jsonl``
* ``ig_translation_scc.jsonl``
* ``ig_translation_scc_edges.jsonl``

It deliberately does not import or mutate the raw ``ig_nodes`` / ``ig_edges``
Lean evidence layer.  All derived documents retain raw ids/hashes for descent.
"""

from __future__ import annotations

import argparse
import json
import subprocess
import sys
from pathlib import Path
from typing import Any

from tools.infra.arango_env import (
    arango_database,
    arango_endpoint,
    arango_password,
    arango_username,
    load_repo_arango_env,
)
from tools.infra.arango_raw_infotree_ingest import (
    ArangoTarget,
    CollectionSpec,
    collection_count,
    create_collection,
    ensure_database,
    ensure_index,
    import_rows,
    iter_jsonl,
    list_collections,
    truncate_collection,
)


DEFAULT_INPUT_DIR = Path("artifacts/expr-graph/wire-topology")

ROW_FILES: dict[str, str] = {
    "ig_wires": "ig_wires.jsonl",
    "ig_gates": "ig_gates.jsonl",
    "ig_wire_edges": "ig_wire_edges.jsonl",
    "ig_scc": "ig_scc.jsonl",
    "ig_scc_edges": "ig_scc_edges.jsonl",
    "ig_decl_topologies": "ig_decl_topologies.jsonl",
    "ig_hashes": "ig_hashes.jsonl",
    "ig_logic_tokens": "ig_logic_tokens.jsonl",
    "ig_logic_vectors": "ig_logic_vectors.jsonl",
    "ig_text_index_docs": "ig_text_index_docs.jsonl",
    "ig_translation_candidates": "ig_translation_candidates.jsonl",
    "ig_translation_edges": "ig_translation_edges.jsonl",
    "ig_translation_scc": "ig_translation_scc.jsonl",
    "ig_translation_scc_edges": "ig_translation_scc_edges.jsonl",
}

COLLECTION_SPECS = [
    CollectionSpec("ig_wires", edge=False),
    CollectionSpec("ig_gates", edge=False),
    CollectionSpec("ig_wire_edges", edge=True),
    CollectionSpec("ig_scc", edge=False),
    CollectionSpec("ig_scc_edges", edge=True),
    CollectionSpec("ig_decl_topologies", edge=False),
    CollectionSpec("ig_hashes", edge=False),
    CollectionSpec("ig_logic_tokens", edge=False),
    CollectionSpec("ig_logic_vectors", edge=False),
    CollectionSpec("ig_text_index_docs", edge=False),
    CollectionSpec("ig_translation_candidates", edge=False),
    CollectionSpec("ig_translation_edges", edge=True),
    CollectionSpec("ig_translation_scc", edge=False),
    CollectionSpec("ig_translation_scc_edges", edge=True),
]

INDEX_SPECS: dict[str, list[dict[str, Any]]] = {
    "ig_wires": [
        {"fields": ["wireKey"], "unique": True},
        {"fields": ["wireHash"]},
        {"fields": ["deBruijnHash"]},
        {"fields": ["incidenceHash"]},
        {"fields": ["decl"]},
        {"fields": ["module"]},
        {"fields": ["binderExpr"]},
        {"fields": ["binderRawId"]},
        {"fields": ["rawBvarId"]},
        {"fields": ["deBruijnIdx"]},
        {"fields": ["quality"]},
        {"fields": ["wireLevel"]},
        {"fields": ["rolePath"]},
        {"fields": ["binderKind"]},
    ],
    "ig_gates": [
        {"fields": ["gateKey"], "unique": True},
        {"fields": ["gateHash"]},
        {"fields": ["decl"]},
        {"fields": ["module"]},
        {"fields": ["gateKind"]},
        {"fields": ["operatorName"]},
        {"fields": ["constName"]},
        {"fields": ["rawExprId"]},
        {"fields": ["constDeclId"]},
        {"fields": ["quality"]},
    ],
    "ig_wire_edges": [
        {"fields": ["kind"]},
        {"fields": ["role"]},
        {"fields": ["source"]},
        {"fields": ["incidenceHash"]},
        {"fields": ["wireHash"]},
        {"fields": ["rawEdgeId"]},
        {"fields": ["_from", "role"]},
        {"fields": ["_to", "role"]},
        {"fields": ["kind", "role"]},
    ],
    "ig_scc": [
        {"fields": ["kind"]},
        {"fields": ["memberCount"]},
        {"fields": ["sccPatternHash"]},
        {"fields": ["quality"]},
    ],
    "ig_scc_edges": [
        {"fields": ["kind"]},
        {"fields": ["role"]},
        {"fields": ["source"]},
        {"fields": ["_from", "role"]},
        {"fields": ["_to", "role"]},
        {"fields": ["kind", "role"]},
    ],
    "ig_decl_topologies": [
        {"fields": ["decl"], "unique": True},
        {"fields": ["module"]},
        {"fields": ["ownerAwareHash"]},
        {"fields": ["patternHash"]},
        {"fields": ["roleHash"]},
        {"fields": ["quality"]},
    ],
    "ig_hashes": [
        {"fields": ["hash"]},
        {"fields": ["hashKind"]},
        {"fields": ["decl"]},
        {"fields": ["module"]},
        {"fields": ["normalization"]},
        {"fields": ["hashKind", "hash"]},
    ],
    "ig_logic_tokens": [
        {"fields": ["decl"]},
        {"fields": ["module"]},
        {"fields": ["hashKind"]},
        {"fields": ["value"]},
        {"fields": ["hashKind", "value"]},
    ],
    "ig_logic_vectors": [
        {"fields": ["decl"], "unique": True},
        {"fields": ["module"]},
        {"fields": ["featureHash"]},
        {"fields": ["featureCount"]},
        {"fields": ["dimension"]},
        {"fields": ["identity.patternHash"]},
        {"fields": ["identity.roleHash"]},
        {"fields": ["identity.ownerAwareHash"]},
    ],
    "ig_text_index_docs": [
        {"fields": ["decl"], "unique": True},
        {"fields": ["module"]},
        {"fields": ["featureHash"]},
        {"fields": ["ownerAwareHash"]},
        {"fields": ["patternHash"]},
        {"fields": ["roleHash"]},
        {"fields": ["reviewOnly"]},
    ],
    "ig_translation_candidates": [
        {"fields": ["sourceDecl"]},
        {"fields": ["targetDecl"]},
        {"fields": ["candidateKind"]},
        {"fields": ["verified"]},
        {"fields": ["verificationTier"]},
        {"fields": ["leanVerified"]},
        {"fields": ["reviewOnly"]},
        {"fields": ["safeForDerivedSCC"]},
        {"fields": ["safeForAutoRewrite"]},
        {"fields": ["proposedTranslation"]},
        {"fields": ["sourceDecl", "targetDecl"]},
    ],
    "ig_translation_edges": [
        {"fields": ["kind"]},
        {"fields": ["translationKind"]},
        {"fields": ["sourceDecl"]},
        {"fields": ["targetDecl"]},
        {"fields": ["translationHash"]},
        {"fields": ["verificationTier"]},
        {"fields": ["leanVerified"]},
        {"fields": ["safeForDerivedSCC"]},
        {"fields": ["safeForDedupSCC"]},
        {"fields": ["safeForAutoRewrite"]},
        {"fields": ["_from", "translationKind"]},
        {"fields": ["_to", "translationKind"]},
    ],
    "ig_translation_scc": [
        {"fields": ["kind"]},
        {"fields": ["memberCount"]},
        {"fields": ["translationSccHash"]},
        {"fields": ["quality"]},
    ],
    "ig_translation_scc_edges": [
        {"fields": ["kind"]},
        {"fields": ["role"]},
        {"fields": ["sourceDecl"]},
        {"fields": ["_from", "role"]},
        {"fields": ["_to", "role"]},
    ],
}


def normalize_wire_row(collection: str, row: dict[str, Any]) -> dict[str, Any]:
    out = dict(row)
    if "_key" not in out or not str(out["_key"]):
        raise ValueError(f"{collection} row is missing _key")
    out["_key"] = str(out["_key"])
    if collection == "ig_wires":
        out.setdefault("wireKey", out["_key"])
    elif collection == "ig_gates":
        out.setdefault("gateKey", out["_key"])
    elif collection == "ig_wire_edges":
        if "_from" not in out or "_to" not in out:
            raise ValueError("ig_wire_edges row is missing _from/_to")
    elif collection == "ig_scc":
        if "sccPatternHash" not in out:
            raise ValueError("ig_scc row is missing sccPatternHash")
    elif collection == "ig_scc_edges":
        if "_from" not in out or "_to" not in out:
            raise ValueError("ig_scc_edges row is missing _from/_to")
    elif collection == "ig_decl_topologies":
        if "decl" not in out or not str(out["decl"]):
            raise ValueError("ig_decl_topologies row is missing decl")
    elif collection == "ig_hashes":
        if "hash" not in out or "hashKind" not in out:
            raise ValueError("ig_hashes row is missing hash/hashKind")
    elif collection == "ig_logic_tokens":
        if "decl" not in out or "value" not in out:
            raise ValueError("ig_logic_tokens row is missing decl/value")
    elif collection == "ig_logic_vectors":
        if "decl" not in out or "logicVector" not in out or "features" not in out:
            raise ValueError("ig_logic_vectors row is missing decl/logicVector/features")
    elif collection == "ig_text_index_docs":
        if "decl" not in out or "logicVector" not in out:
            raise ValueError("ig_text_index_docs row is missing decl/logicVector")
    elif collection == "ig_translation_candidates":
        if "sourceDecl" not in out or "targetDecl" not in out or "candidateKind" not in out:
            raise ValueError("ig_translation_candidates row is missing sourceDecl/targetDecl/candidateKind")
    elif collection == "ig_translation_edges":
        if "_from" not in out or "_to" not in out or "translationKind" not in out:
            raise ValueError("ig_translation_edges row is missing _from/_to/translationKind")
    elif collection == "ig_translation_scc":
        if "translationSccHash" not in out:
            raise ValueError("ig_translation_scc row is missing translationSccHash")
    elif collection == "ig_translation_scc_edges":
        if "_from" not in out or "_to" not in out:
            raise ValueError("ig_translation_scc_edges row is missing _from/_to")
    else:
        raise ValueError(f"unknown wire topology collection: {collection}")
    return out


def wire_index_specs() -> dict[str, list[dict[str, Any]]]:
    return {
        collection: [dict(spec) for spec in specs]
        for collection, specs in INDEX_SPECS.items()
    }


def ensure_wire_indexes(target: ArangoTarget) -> dict[str, Any]:
    report: dict[str, Any] = {}
    for collection, specs in INDEX_SPECS.items():
        collection_report = []
        for spec in specs:
            fields = [str(field) for field in spec["fields"]]
            try:
                result = ensure_index(target, collection, fields, unique=bool(spec.get("unique", False)))
                collection_report.append(
                    {
                        "fields": fields,
                        "unique": bool(spec.get("unique", False)),
                        "error": bool(result.get("error")) if isinstance(result, dict) else False,
                        "id": result.get("id") if isinstance(result, dict) else None,
                        "isNewlyCreated": result.get("isNewlyCreated") if isinstance(result, dict) else None,
                    }
                )
            except Exception as exc:
                collection_report.append(
                    {"fields": fields, "unique": bool(spec.get("unique", False)), "error": True, "message": str(exc)}
                )
        report[collection] = collection_report
    return report


def ensure_wire_collections(target: ArangoTarget, *, truncate: bool) -> dict[str, Any]:
    ensure_database(target)
    existing = list_collections(target)
    report: dict[str, Any] = {"created": [], "existing": [], "truncated": []}
    for spec in COLLECTION_SPECS:
        if spec.name not in existing:
            create_collection(target, spec)
            report["created"].append(spec.name)
        else:
            report["existing"].append(spec.name)
        if truncate:
            truncate_collection(target, spec.name)
            report["truncated"].append(spec.name)
    return report


def preflight(input_dir: Path) -> dict[str, Any]:
    missing = [name for name in ROW_FILES.values() if not (input_dir / name).exists()]
    counts = {
        collection: sum(1 for _ in iter_jsonl(input_dir / filename))
        for collection, filename in ROW_FILES.items()
        if (input_dir / filename).exists()
    }
    return {"input_dir": str(input_dir), "missing_files": missing, "counts": counts}


def ingest_wire_topology(
    input_dir: Path,
    target: ArangoTarget,
    *,
    truncate: bool,
    skip_indexes: bool,
    batch_size: int,
) -> dict[str, Any]:
    pf = preflight(input_dir)
    if pf["missing_files"]:
        raise RuntimeError(f"wire topology input preflight failed: missing {pf['missing_files']}")

    report: dict[str, Any] = {
        "schema": "info_geometry.arango_wire_topology_ingest.v1",
        "truth_boundary": "derived projection; raw Lean evidence remains ig_nodes/ig_edges",
        "input_dir": str(input_dir),
        "preflight": pf,
        "collections": ensure_wire_collections(target, truncate=truncate),
        "imports": {},
    }

    for collection, filename in ROW_FILES.items():
        path = input_dir / filename
        rows = (normalize_wire_row(collection, row) for row in iter_jsonl(path))
        report["imports"][collection] = import_rows(
            target,
            collection,
            rows,
            batch_size=batch_size,
        )

    if not skip_indexes:
        report["indexes"] = ensure_wire_indexes(target)
    report["live_counts"] = {spec.name: collection_count(target, spec.name) for spec in COLLECTION_SPECS}
    return report


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input-dir", type=Path, default=DEFAULT_INPUT_DIR)
    parser.add_argument("--endpoint", default=None)
    parser.add_argument("--database", default=None)
    parser.add_argument("--username", default=None)
    parser.add_argument("--password", default=None)
    parser.add_argument("--truncate", action="store_true")
    parser.add_argument("--skip-indexes", action="store_true")
    parser.add_argument("--batch-size", type=int, default=1000)
    parser.add_argument("--json-out", type=Path, default=Path("artifacts/expr-graph/arango_wire_topology_ingest_report.json"))
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    load_repo_arango_env()
    target = ArangoTarget(
        endpoint=args.endpoint or arango_endpoint(),
        database=args.database or arango_database(),
        username=args.username or arango_username(),
        password=args.password or arango_password(),
    )

    try:
        report = ingest_wire_topology(
            args.input_dir,
            target,
            truncate=bool(args.truncate),
            skip_indexes=bool(args.skip_indexes),
            batch_size=int(args.batch_size),
        )
    except subprocess.CalledProcessError as exc:
        print(str(exc), file=sys.stderr)
        return exc.returncode or 1
    except Exception as exc:
        print(str(exc), file=sys.stderr)
        return 1

    args.json_out.parent.mkdir(parents=True, exist_ok=True)
    args.json_out.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(f"Wire topology Arango ingest report written: {args.json_out}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
