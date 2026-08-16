#!/usr/bin/env python3
"""Materialize translation candidates and derived/Lean-verified translation edges.

This layer separates approximate retrieval from exact structural verification:

* ``ig_translation_candidates.jsonl`` records review candidates from exact hash
  buckets or logic-vector cosine similarity.
* ``ig_translation_edges.jsonl`` records derived translation edges when an exact
  canonical condition holds, and Lean/kernel translation edges only when an
  explicit certificate is supplied.
* ``ig_translation_scc.jsonl`` and ``ig_translation_scc_edges.jsonl`` are SCCs
  of the derived translation graph.

Cosine similarity never creates a verified edge by itself.
Python never proves theorem equivalence; ``leanVerified`` is true only for
certificate-backed edges.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import math
import sys
from collections import defaultdict
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Iterable

ROOT = Path(__file__).resolve().parents[2]
_SRC = ROOT / "src"
if str(_SRC) not in sys.path:
    sys.path.insert(0, str(_SRC))
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from igf.common.json_io import iter_jsonl, write_jsonl
from igf.common.time_utils import utc_now_iso


DEFAULT_WIRE_DIR = Path("artifacts/expr-graph/wire-topology")
DEFAULT_VECTOR_DIR = Path("artifacts/expr-graph/logic-vectors")
DEFAULT_OUTPUT_DIR = Path("artifacts/expr-graph/translation-candidates")


# [lossless-compact] stable_hash folded into igf.common.hashing.stable_hash
from igf.common.hashing import stable_hash


def stable_key(prefix: str, *parts: Any) -> str:
    return prefix + "_" + stable_hash(*parts).split(":", 1)[1][:32]


def load_lean_equivalence_certs(path: Path | None) -> dict[tuple[str, str], dict[str, Any]]:
    if path is None:
        return {}
    certs: dict[tuple[str, str], dict[str, Any]] = {}
    for row in iter_jsonl(path):
        source = str(row.get("sourceDecl", "") or row.get("source", "") or "")
        target = str(row.get("targetDecl", "") or row.get("target", "") or "")
        if not source or not target or source == target:
            continue
        lean_verified = bool(row.get("leanVerified", row.get("kernelVerified", False)))
        if not lean_verified:
            continue
        certs[(source, target)] = {
            "certificateHash": str(row.get("certificateHash", "") or row.get("proofHash", "") or ""),
            "certificatePath": str(row.get("certificatePath", "") or row.get("path", "") or ""),
            "certificateKind": str(row.get("certificateKind", "") or "lean_kernel_equivalence"),
            "verificationTier": str(row.get("verificationTier", "") or "lean_kernel"),
            "safeForAutoRewrite": bool(row.get("safeForAutoRewrite", True)),
            "checker": str(row.get("checker", "") or "lean"),
        }
    return certs


def cosine(left: list[float], right: list[float]) -> float:
    if not left or not right or len(left) != len(right):
        return 0.0
    dot = sum(a * b for a, b in zip(left, right))
    lnorm = math.sqrt(sum(a * a for a in left))
    rnorm = math.sqrt(sum(b * b for b in right))
    if lnorm == 0.0 or rnorm == 0.0:
        return 0.0
    return dot / (lnorm * rnorm)


def token_signature(row: dict[str, Any], mode: str) -> list[str]:
    return sorted(str(token) for token in row.get(mode + "Tokens", []) or [])


def canonical_role_swap_tokens(tokens: list[str]) -> list[str]:
    swapped: list[str] = []
    for token in tokens:
        text = str(token)
        text = text.replace("projectorRole:left:P0", "__TMP_LEFT_P0__")
        text = text.replace("projectorRole:right:P0", "__TMP_RIGHT_P0__")
        text = text.replace("projectorRole:left:P", "projectorRole:left:P0")
        text = text.replace("projectorRole:right:P", "projectorRole:right:P0")
        text = text.replace("__TMP_LEFT_P0__", "projectorRole:left:P")
        text = text.replace("__TMP_RIGHT_P0__", "projectorRole:right:P")
        swapped.append(text)
    return sorted(swapped)


def add_candidate(
    candidates: dict[tuple[str, str, str], dict[str, Any]],
    source: str,
    target: str,
    kind: str,
    *,
    signals: dict[str, Any],
    proposed_translation: str,
    verified: bool,
    verification_tier: str,
    lean_verified: bool = False,
    safe_for_auto_rewrite: bool = False,
) -> None:
    if not source or not target or source == target:
        return
    key = (source, target, kind)
    existing = candidates.get(key)
    if existing is None:
        candidates[key] = {
            "_key": stable_key("tc", source, target, kind),
            "sourceDecl": source,
            "targetDecl": target,
            "candidateKind": kind,
            "proposedTranslation": proposed_translation,
            "signals": signals,
            "verified": verified,
            "verificationTier": verification_tier,
            "leanVerified": lean_verified,
            "reviewOnly": not verified,
            "safeForDerivedSCC": verified,
            "safeForDedupSCC": verified,
            "safeForAutoRewrite": safe_for_auto_rewrite,
        }
        return
    existing["signals"].update(signals)
    existing["verified"] = bool(existing.get("verified")) or verified
    existing["leanVerified"] = bool(existing.get("leanVerified")) or lean_verified
    existing["reviewOnly"] = not bool(existing["verified"])
    existing["safeForDerivedSCC"] = bool(existing.get("safeForDerivedSCC")) or verified
    existing["safeForDedupSCC"] = bool(existing.get("safeForDedupSCC")) or verified
    existing["safeForAutoRewrite"] = bool(existing.get("safeForAutoRewrite")) or safe_for_auto_rewrite
    if lean_verified:
        existing["verificationTier"] = verification_tier


def strongly_connected_components(vertices: set[str], edges: list[tuple[str, str]]) -> list[list[str]]:
    adjacency: dict[str, list[str]] = defaultdict(list)
    for source, target in edges:
        adjacency[source].append(target)

    index = 0
    stack: list[str] = []
    on_stack: set[str] = set()
    indices: dict[str, int] = {}
    lowlinks: dict[str, int] = {}
    components: list[list[str]] = []

    def connect(vertex: str) -> None:
        nonlocal index
        indices[vertex] = index
        lowlinks[vertex] = index
        index += 1
        stack.append(vertex)
        on_stack.add(vertex)

        for target in adjacency.get(vertex, []):
            if target not in indices:
                connect(target)
                lowlinks[vertex] = min(lowlinks[vertex], lowlinks[target])
            elif target in on_stack:
                lowlinks[vertex] = min(lowlinks[vertex], indices[target])

        if lowlinks[vertex] == indices[vertex]:
            component: list[str] = []
            while True:
                target = stack.pop()
                on_stack.remove(target)
                component.append(target)
                if target == vertex:
                    break
            components.append(sorted(component))

    for vertex in sorted(vertices):
        if vertex not in indices:
            connect(vertex)
    return components


def materialize(
    wire_dir: Path,
    vector_dir: Path,
    output_dir: Path,
    *,
    cosine_threshold: float,
    lean_equivalence_certs: Path | None = None,
) -> dict[str, Any]:
    lean_certs = load_lean_equivalence_certs(lean_equivalence_certs)
    topology_by_decl: dict[str, dict[str, Any]] = {}
    for row in iter_jsonl(wire_dir / "ig_decl_topologies.jsonl"):
        decl = str(row.get("decl", "") or "")
        if decl:
            topology_by_decl[decl] = row

    vectors_by_decl: dict[str, dict[str, Any]] = {}
    for row in iter_jsonl(vector_dir / "ig_logic_vectors.jsonl"):
        decl = str(row.get("decl", "") or "")
        if decl:
            vectors_by_decl[decl] = row

    candidates: dict[tuple[str, str, str], dict[str, Any]] = {}
    decls = sorted(set(topology_by_decl) | set(vectors_by_decl))

    for hash_kind in ["ownerAwareHash", "patternHash", "roleHash"]:
        buckets: dict[str, list[str]] = defaultdict(list)
        for decl, row in topology_by_decl.items():
            hash_value = str(row.get(hash_kind, "") or "")
            if hash_value:
                buckets[hash_value].append(decl)
        for hash_value, members in buckets.items():
            if len(members) < 2:
                continue
            for source in sorted(members):
                for target in sorted(members):
                    if source == target:
                        continue
                    add_candidate(
                        candidates,
                        source,
                        target,
                        f"same_{hash_kind}",
                        signals={hash_kind: hash_value},
                        proposed_translation=f"identity:{hash_kind}",
                        verified=True,
                        verification_tier="derived_canonical_hash",
                    )

    for source in decls:
        source_row = topology_by_decl.get(source, {})
        source_tokens = token_signature(source_row, "roleHash")
        if not source_tokens:
            continue
        swapped = canonical_role_swap_tokens(source_tokens)
        if swapped == source_tokens:
            continue
        for target in decls:
            if source == target:
                continue
            target_tokens = token_signature(topology_by_decl.get(target, {}), "roleHash")
            if target_tokens and swapped == target_tokens:
                add_candidate(
                    candidates,
                    source,
                    target,
                    "role_swap",
                    signals={"roleTokensCanonicalized": True},
                    proposed_translation="swap:P:P0",
                    verified=True,
                    verification_tier="derived_role_token",
                )

    for i, source in enumerate(decls):
        source_vec = vectors_by_decl.get(source, {}).get("logicVector", [])
        if not isinstance(source_vec, list) or not source_vec:
            continue
        for target in decls[i + 1 :]:
            target_vec = vectors_by_decl.get(target, {}).get("logicVector", [])
            if not isinstance(target_vec, list) or not target_vec:
                continue
            sim = cosine([float(x) for x in source_vec], [float(x) for x in target_vec])
            if sim >= cosine_threshold:
                signal = {"logicVectorCosine": round(sim, 8), "cosineThreshold": cosine_threshold}
                add_candidate(
                    candidates,
                    source,
                    target,
                    "logic_vector_near",
                    signals=signal,
                    proposed_translation="unknown",
                    verified=False,
                    verification_tier="vector_review",
                )
                add_candidate(
                    candidates,
                    target,
                    source,
                    "logic_vector_near",
                    signals=signal,
                    proposed_translation="unknown",
                    verified=False,
                    verification_tier="vector_review",
                )

    for (source, target), cert in sorted(lean_certs.items()):
        add_candidate(
            candidates,
            source,
            target,
            "lean_kernel_equivalence",
            signals={"leanEquivalenceCertificate": cert},
            proposed_translation="lean_kernel_equivalence",
            verified=True,
            verification_tier=str(cert.get("verificationTier", "") or "lean_kernel"),
            lean_verified=True,
            safe_for_auto_rewrite=bool(cert.get("safeForAutoRewrite", True)),
        )

    candidate_rows = sorted(candidates.values(), key=lambda row: (row["sourceDecl"], row["targetDecl"], row["candidateKind"]))
    edge_rows: list[dict[str, Any]] = []
    verified_graph_edges: list[tuple[str, str]] = []
    vertices: set[str] = set()
    for row in candidate_rows:
        if not row.get("safeForDerivedSCC", row.get("verified")):
            continue
        source = str(row["sourceDecl"])
        target = str(row["targetDecl"])
        vertices.add(source)
        vertices.add(target)
        verified_graph_edges.append((source, target))
        edge_rows.append(
            {
                "_key": stable_key("te", source, target, row["candidateKind"], row["proposedTranslation"]),
                "_from": f"ig_decl_topologies/{stable_key('topo', source)}",
                "_to": f"ig_decl_topologies/{stable_key('topo', target)}",
                "kind": "verified_translation",
                "sourceDecl": source,
                "targetDecl": target,
                "translationKind": row["candidateKind"],
                "proposedTranslation": row["proposedTranslation"],
                "translationHash": stable_hash(row["candidateKind"], row["proposedTranslation"], source, target),
                "verification": row.get("verificationTier", "derived_canonical_hash"),
                "verificationTier": row.get("verificationTier", "derived_canonical_hash"),
                "proofAuthority": "lean-kernel-certificate" if row.get("leanVerified") else "derived-canonical-check-not-Lean-theorem",
                "leanVerified": bool(row.get("leanVerified", False)),
                "safeForDerivedSCC": bool(row.get("safeForDerivedSCC", True)),
                "safeForDedupSCC": bool(row.get("safeForDedupSCC", True)),
                "safeForAutoRewrite": bool(row.get("safeForAutoRewrite", False)),
            }
        )

    scc_rows: list[dict[str, Any]] = []
    scc_edge_rows: list[dict[str, Any]] = []
    for component in strongly_connected_components(vertices, verified_graph_edges):
        scc_hash = stable_hash("translation-scc", json.dumps(component, sort_keys=True))
        scc_key = stable_key("tscc", scc_hash)
        scc_id = f"ig_translation_scc/{scc_key}"
        scc_rows.append(
            {
                "_key": scc_key,
                "kind": "translation_scc",
                "memberCount": len(component),
                "members": component,
                "translationSccHash": scc_hash,
                "quality": "derived",
            }
        )
        for member in component:
            scc_edge_rows.append(
                {
                    "_key": stable_key("tse", "member_of_translation_scc", member, scc_id),
                    "_from": f"ig_decl_topologies/{stable_key('topo', member)}",
                    "_to": scc_id,
                    "kind": "member_of_translation_scc",
                    "role": "member_of_translation_scc",
                    "sourceDecl": member,
                }
            )

    counts = {
        "ig_translation_candidates": write_jsonl(output_dir / "ig_translation_candidates.jsonl", candidate_rows),
        "ig_translation_edges": write_jsonl(output_dir / "ig_translation_edges.jsonl", edge_rows),
        "ig_translation_scc": write_jsonl(output_dir / "ig_translation_scc.jsonl", scc_rows),
        "ig_translation_scc_edges": write_jsonl(output_dir / "ig_translation_scc_edges.jsonl", scc_edge_rows),
    }
    metadata = {
        "schema": "info_geometry.translation_candidates.v1",
        "generated_at": utc_now_iso(),
        "wire_dir": str(wire_dir),
        "vector_dir": str(vector_dir),
        "output_dir": str(output_dir),
        "cosine_threshold": cosine_threshold,
        "lean_equivalence_certs": str(lean_equivalence_certs) if lean_equivalence_certs else "",
        "counts": counts,
        "truth_boundary": "cosine candidates are review-only; derived edges require exact canonical checks; Lean/kernel equivalence requires explicit certificate rows",
    }
    output_dir.mkdir(parents=True, exist_ok=True)
    (output_dir / "metadata.json").write_text(json.dumps(metadata, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return metadata


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--wire-dir", type=Path, default=DEFAULT_WIRE_DIR)
    parser.add_argument("--vector-dir", type=Path, default=DEFAULT_VECTOR_DIR)
    parser.add_argument("--output-dir", type=Path, default=DEFAULT_OUTPUT_DIR)
    parser.add_argument("--cosine-threshold", type=float, default=0.85)
    parser.add_argument("--lean-equivalence-certs", type=Path, default=None)
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    metadata = materialize(
        args.wire_dir,
        args.vector_dir,
        args.output_dir,
        cosine_threshold=float(args.cosine_threshold),
        lean_equivalence_certs=args.lean_equivalence_certs,
    )
    print(json.dumps(metadata, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
