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
* ``ig_kernel_equivalence_edges.jsonl`` when kernel certificates have been materialized
* ``ig_triple_homomorphism_edges.jsonl`` when finite triple certificates have been materialized

It deliberately does not import or mutate the raw ``ig_nodes`` / ``ig_edges``
Lean evidence layer.  All derived documents retain raw ids/hashes for descent.
"""

from __future__ import annotations

import argparse
import hashlib
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
    db_url,
    request_json,
    truncate_collection,
)


DEFAULT_INPUT_DIR = Path("artifacts/expr-graph/wire-topology")
OPTIONAL_ROW_COLLECTIONS = frozenset({
    "ig_kernel_equivalence_edges",
    "ig_triple_homomorphism_edges",
})

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
    "ig_kernel_equivalence_edges": "ig_kernel_equivalence_edges.jsonl",
    "ig_triple_homomorphism_edges": "ig_triple_homomorphism_edges.jsonl",
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
    CollectionSpec("ig_kernel_equivalence_edges", edge=True),
    CollectionSpec("ig_triple_homomorphism_edges", edge=True),
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
    "ig_kernel_equivalence_edges": [
        {"fields": ["kind"]},
        {"fields": ["status"]},
        {"fields": ["mode"]},
        {"fields": ["sourceDecl"]},
        {"fields": ["targetDecl"]},
        {"fields": ["verificationTier"]},
        {"fields": ["proofAuthority"]},
        {"fields": ["leanVerified"]},
        {"fields": ["kernelTypeDefEq"]},
        {"fields": ["kernelValueDefEq"]},
        {"fields": ["safeForAutoRewrite"]},
        {"fields": ["graphUse"]},
        {"fields": ["candidatePairHash"]},
        {"fields": ["certificateHash"]},
        {"fields": ["_from", "kind"]},
        {"fields": ["_to", "kind"]},
    ],
    "ig_triple_homomorphism_edges": [
        {"fields": ["kind"]},
        {"fields": ["status"]},
        {"fields": ["sourceId"]},
        {"fields": ["targetId"]},
        {"fields": ["sourceLabel"]},
        {"fields": ["targetLabel"]},
        {"fields": ["verificationTier"]},
        {"fields": ["proofAuthority"]},
        {"fields": ["checker"]},
        {"fields": ["leanVerified"]},
        {"fields": ["safeForDedupSCC"]},
        {"fields": ["safeForAutoRewrite"]},
        {"fields": ["graphUse"]},
        {"fields": ["candidatePairHash"]},
        {"fields": ["certificateHash"]},
        {"fields": ["missingTripleHash"]},
        {"fields": ["_from", "kind"]},
        {"fields": ["_to", "kind"]},
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
    elif collection == "ig_kernel_equivalence_edges":
        if "_from" not in out or "_to" not in out or "mode" not in out:
            raise ValueError("ig_kernel_equivalence_edges row is missing _from/_to/mode")
        out.setdefault("kind", "kernel_equivalence_certificate")
    elif collection == "ig_triple_homomorphism_edges":
        if "_from" not in out or "_to" not in out or "status" not in out:
            raise ValueError("ig_triple_homomorphism_edges row is missing _from/_to/status")
        out.setdefault("kind", "triple_homomorphism_certificate")
    else:
        raise ValueError(f"unknown wire topology collection: {collection}")
    return out


def wire_index_specs() -> dict[str, list[dict[str, Any]]]:
    return {
        collection: [dict(spec) for spec in specs]
        for collection, specs in INDEX_SPECS.items()
    }


def active_collections(input_dir: Path) -> set[str]:
    return {
        collection
        for collection, filename in ROW_FILES.items()
        if collection not in OPTIONAL_ROW_COLLECTIONS or (input_dir / filename).exists()
    }


def ensure_wire_indexes(target: ArangoTarget, collections: set[str] | None = None) -> dict[str, Any]:
    report: dict[str, Any] = {}
    for collection, specs in INDEX_SPECS.items():
        if collections is not None and collection not in collections:
            continue
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


def ensure_wire_indexes_for_generation(
    target: ArangoTarget, active: set[str], collection_map: dict[str, str]
) -> dict[str, Any]:
    report: dict[str, Any] = {}
    for base_collection in sorted(active):
        target_collection = collection_map[base_collection]
        entries = []
        for spec in INDEX_SPECS.get(base_collection, []):
            fields = [str(field) for field in spec["fields"]]
            try:
                result = ensure_index(target, target_collection, fields, unique=bool(spec.get("unique", False)))
                entries.append({"fields": fields, "error": bool(result.get("error")), "id": result.get("id")})
            except Exception as exc:
                entries.append({"fields": fields, "error": True, "message": str(exc)})
        if entries:
            report[target_collection] = entries
    return report


def remap_wire_endpoints(row: dict[str, Any], collection_map: dict[str, str]) -> dict[str, Any]:
    out = dict(row)
    for field in ("_from", "_to"):
        if field not in out:
            continue
        collection, separator, key = str(out[field]).partition("/")
        if separator and collection in collection_map:
            out[field] = f"{collection_map[collection]}/{key}"
    return out


def generation_fingerprint(input_dir: Path, build_fingerprint: str, active: set[str]) -> str:
    digest = hashlib.sha256(build_fingerprint.encode("utf-8"))
    for collection in sorted(active):
        path = input_dir / ROW_FILES[collection]
        digest.update(path.name.encode("utf-8"))
        with path.open("rb") as stream:
            for chunk in iter(lambda: stream.read(1024 * 1024), b""):
                digest.update(chunk)
    return digest.hexdigest()[:24]


def canonical_json(value: Any) -> str:
    return json.dumps(value, sort_keys=True, ensure_ascii=False, separators=(",", ":"))


def archetype_hash_bundles(input_dir: Path) -> list[tuple[dict[str, Any], str]]:
    """Build content-addressed coarse signatures from SCC and declaration hashes.

    These signatures are retrieval archetypes, not proofs of equivalence.
    """
    declaration_hashes: dict[str, dict[str, str]] = {}
    for row in iter_jsonl(input_dir / ROW_FILES["ig_decl_topologies"]):
        decl = str(row.get("decl") or "")
        if decl:
            declaration_hashes[decl] = {
                field: str(row[field])
                for field in ("patternHash", "roleHash")
                if row.get(field)
            }

    out: list[tuple[dict[str, Any], str]] = []
    for scc in iter_jsonl(input_dir / ROW_FILES["ig_scc"]):
        pattern_hashes = sorted({
            (kind, declaration_hashes[decl][kind])
            for decl in (str(x) for x in scc.get("decls", []))
            for kind in ("patternHash", "roleHash")
            if decl in declaration_hashes and kind in declaration_hashes[decl]
        })
        bundle = {
            "scheme": "info_geometry.archetype_hash_bundle.v1",
            "sccPatternHash": str(scc.get("sccPatternHash") or ""),
            "declarationPatternAndRoleHashes": [
                {"kind": kind, "hash": value} for kind, value in pattern_hashes
            ],
        }
        serialized = canonical_json(bundle)
        key = "arch_" + hashlib.sha256(serialized.encode("utf-8")).hexdigest()
        out.append((bundle, key))
    return out


def insert_immutable_signature(target: ArangoTarget, document: dict[str, Any]) -> None:
    collection = "ig_archetype_signatures"
    try:
        request_json(
            "POST", db_url(target, f"/_api/document/{collection}?waitForSync=true"),
            username=target.username, password=target.password, payload=document,
        )
    except RuntimeError as exc:
        if "1210" not in str(exc):
            raise
        existing = request_json(
            "GET", db_url(target, f"/_api/document/{collection}/{document['_key']}"),
            username=target.username, password=target.password,
        )
        actual = {k: v for k, v in existing.items() if k not in {"_id", "_key", "_rev"}}
        expected = {k: v for k, v in document.items() if k != "_key"}
        if canonical_json(actual) != canonical_json(expected):
            raise RuntimeError(f"archetype hash collision for {document['_key']}") from exc


def ensure_wire_collections(
    target: ArangoTarget,
    *,
    truncate: bool,
    collections: set[str] | None = None,
) -> dict[str, Any]:
    ensure_database(target)
    existing = list_collections(target)
    report: dict[str, Any] = {"created": [], "existing": [], "truncated": [], "skipped": []}
    for spec in COLLECTION_SPECS:
        if collections is not None and spec.name not in collections:
            report["skipped"].append(spec.name)
            continue
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
    missing = [
        name
        for collection, name in ROW_FILES.items()
        if collection not in OPTIONAL_ROW_COLLECTIONS and not (input_dir / name).exists()
    ]
    optional_missing = [
        name
        for collection, name in ROW_FILES.items()
        if collection in OPTIONAL_ROW_COLLECTIONS and not (input_dir / name).exists()
    ]
    counts = {
        collection: sum(1 for _ in iter_jsonl(input_dir / filename))
        for collection, filename in ROW_FILES.items()
        if (input_dir / filename).exists()
    }
    return {
        "input_dir": str(input_dir),
        "missing_files": missing,
        "optional_missing_files": optional_missing,
        "counts": counts,
    }


def ingest_wire_topology(
    input_dir: Path,
    target: ArangoTarget,
    *,
    truncate: bool,
    skip_indexes: bool,
    batch_size: int,
    build_fingerprint: str | None = None,
) -> dict[str, Any]:
    pf = preflight(input_dir)
    if pf["missing_files"]:
        raise RuntimeError(f"wire topology input preflight failed: missing {pf['missing_files']}")
    active = active_collections(input_dir)
    generation_id = generation_fingerprint(input_dir, build_fingerprint, active) if build_fingerprint else None
    if generation_id and truncate:
        raise ValueError("--truncate is incompatible with immutable generation ingest")
    collection_map = {
        name: f"{name}_g_{generation_id}" if generation_id else name
        for name in ROW_FILES
    }
    target_specs = [
        CollectionSpec(collection_map[spec.name], spec.edge)
        for spec in COLLECTION_SPECS if spec.name in active
    ]

    report: dict[str, Any] = {
        "schema": "info_geometry.arango_wire_topology_ingest.v1",
        "truth_boundary": "derived projection; raw Lean evidence remains ig_nodes/ig_edges",
        "input_dir": str(input_dir),
        "preflight": pf,
        "active_collections": sorted(active),
        "inactive_optional_collections": sorted(OPTIONAL_ROW_COLLECTIONS - active),
        "generation_id": generation_id,
        "build_fingerprint": build_fingerprint,
        "collections": ensure_wire_collections(
            target, truncate=truncate,
            collections=set() if generation_id else active,
        ) if not generation_id else {},
        "imports": {},
    }

    if generation_id:
        ensure_database(target)
        existing = list_collections(target)
        if any(spec.name in existing for spec in target_specs):
            raise RuntimeError(f"immutable wire-topology generation {generation_id} already exists")
        for spec in target_specs:
            create_collection(target, spec)
        report["collections"] = {"created": [spec.name for spec in target_specs], "truncated": []}

    for collection, filename in ROW_FILES.items():
        path = input_dir / filename
        if collection in OPTIONAL_ROW_COLLECTIONS and not path.exists():
            report["imports"][collection] = {
                "skipped": True,
                "reason": "optional input file is absent",
                "file": str(path),
            }
            continue
        rows = (normalize_wire_row(collection, row) for row in iter_jsonl(path))
        if generation_id:
            rows = (remap_wire_endpoints(row, collection_map) for row in rows)
        target_collection = collection_map[collection]
        report["imports"][target_collection] = import_rows(
            target,
            target_collection,
            rows,
            batch_size=batch_size,
        )

    if not skip_indexes:
        if generation_id:
            report["indexes"] = ensure_wire_indexes_for_generation(target, active, collection_map)
        else:
            report["indexes"] = ensure_wire_indexes(target, active)
    report["live_counts"] = {
        collection_map[spec.name]: collection_count(target, collection_map[spec.name])
        for spec in COLLECTION_SPECS if spec.name in active
    }
    if generation_id:
        existing = list_collections(target)
        signature_collection = "ig_archetype_signatures"
        occurrence_collection = "ig_archetype_occurrences"
        if signature_collection not in existing:
            create_collection(target, CollectionSpec(signature_collection, False))
        if occurrence_collection not in existing:
            create_collection(target, CollectionSpec(occurrence_collection, True))
        bundle_rows = archetype_hash_bundles(input_dir)
        occurrence_edges = []
        for scc, (bundle, signature_key) in zip(iter_jsonl(input_dir / ROW_FILES["ig_scc"]), bundle_rows):
            signature = {
                "_key": signature_key,
                "schema": bundle["scheme"],
                "hashBundle": bundle,
                "hashBundleSha256": signature_key.removeprefix("arch_"),
                "identityScope": "coarse structural archetype; retrieval/dedup index, not proof identity",
            }
            insert_immutable_signature(target, signature)
            occurrence_edges.append({
                "_key": "arche_" + hashlib.sha256(
                    f"{generation_id}:{scc['_key']}:{signature_key}".encode("utf-8")
                ).hexdigest(),
                "_from": f"{collection_map['ig_scc']}/{scc['_key']}",
                "_to": f"ig_archetype_signatures/{signature_key}",
                "role": "scc_has_archetype_signature",
                "generationId": generation_id,
                "sccPatternHash": bundle["sccPatternHash"],
            })
        report["archetype_signature_count"] = len(bundle_rows)
        if not skip_indexes:
            report["archetype_indexes"] = {
                "signatures": [
                    ensure_index(target, "ig_archetype_signatures", ["hashBundleSha256"], unique=True),
                    ensure_index(target, "ig_archetype_signatures", ["hashBundle.sccPatternHash"]),
                ],
                "occurrences": [
                    ensure_index(target, occurrence_collection, ["generationId"]),
                    ensure_index(target, occurrence_collection, ["_to"]),
                ],
            }
        report["imports"][occurrence_collection] = import_rows(
            target, occurrence_collection, occurrence_edges, batch_size=batch_size,
        )
        report["occurrence_edge_count"] = len(occurrence_edges)
        generation_collection = "ig_graph_generations"
        existing = list_collections(target)
        if generation_collection not in existing:
            create_collection(target, CollectionSpec(generation_collection, False))
        generation_doc = {
            "_key": generation_id,
            "schema": "info_geometry.graph_generation.v1",
            "status": "complete",
            "buildFingerprint": build_fingerprint,
            "inputFingerprint": generation_id,
            "collections": {name: collection_map[name] for name in active},
            "signatureEdges": occurrence_collection,
            "liveCounts": report["live_counts"],
            "archetypeSignatureCount": len(bundle_rows),
        }
        request_json(
            "POST", db_url(target, f"/_api/document/{generation_collection}?waitForSync=true"),
            username=target.username, password=target.password, payload=generation_doc,
        )
    return report


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input-dir", type=Path, default=DEFAULT_INPUT_DIR)
    parser.add_argument("--endpoint", default=None)
    parser.add_argument("--database", default=None)
    parser.add_argument("--username", default=None)
    parser.add_argument("--password", default=None)
    parser.add_argument("--truncate", action="store_true")
    parser.add_argument("--build-fingerprint", help="Enable immutable generation ingest bound to the exact Lean/Lake build environment.")
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
            build_fingerprint=args.build_fingerprint,
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
