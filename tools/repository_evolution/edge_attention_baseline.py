#!/usr/bin/env python3
"""Create source-bound cosine logits for the typed repository edge overlay.

This deterministic baseline scores an observed dependency edge by cosine
similarity of its endpoint code embeddings. It is not trained attention,
causal importance, or semantic evidence. Its purpose is to provide a runnable
and provenance-bound comparison point for later reviewed edge-ranking models.
"""
from __future__ import annotations

import argparse
import gzip
import hashlib
import json
import math
import os
import sys
from pathlib import Path
from typing import Any

_REPOSITORY_ROOT = Path(__file__).resolve().parents[2]
if str(_REPOSITORY_ROOT) not in sys.path:
    sys.path.insert(0, str(_REPOSITORY_ROOT))

from tools.repository_evolution.attention_scc import DEPENDENCY_KINDS, edge_reference
from tools.repository_evolution.generation_manifest import (
    validate_current_source_generation_manifest,
)
from tools.repository_evolution.latent_taxonomy import build_encoder_embedding_packet


MAP_SCHEMA = "info_geometry.refactoring_map.v1"
SCORE_SCHEMA = "info_geometry.edge_attention_logits.v1"
MODEL_VERSION = "endpoint_cosine_affinity_baseline.v1"


def _read_json(path: Path) -> dict[str, Any]:
    opener = gzip.open if path.suffix == ".gz" else open
    with opener(path, "rt", encoding="utf-8") as stream:
        value = json.load(stream)
    if not isinstance(value, dict):
        raise ValueError(f"{path}: expected a JSON object")
    return value


def _read_jsonl(path: Path) -> list[dict[str, Any]]:
    rows = []
    with path.open("r", encoding="utf-8") as stream:
        for line_number, line in enumerate(stream, 1):
            if not line.strip():
                continue
            try:
                value = json.loads(line)
            except json.JSONDecodeError as exc:
                raise ValueError(f"{path}:{line_number}: invalid JSON") from exc
            if not isinstance(value, dict):
                raise ValueError(f"{path}:{line_number}: expected an object")
            rows.append(value)
    return rows


def _cosine(left: list[float], right: list[float]) -> float:
    if len(left) != len(right):
        raise ValueError("embedding dimensions differ")
    left_scale = max((abs(value) for value in left), default=0.0)
    right_scale = max((abs(value) for value in right), default=0.0)
    if left_scale == 0.0 or right_scale == 0.0:
        return 0.0
    left_unit = [value / left_scale for value in left]
    right_unit = [value / right_scale for value in right]
    dot = math.fsum(a * b for a, b in zip(left_unit, right_unit))
    left_norm = math.sqrt(math.fsum(value * value for value in left_unit))
    right_norm = math.sqrt(math.fsum(value * value for value in right_unit))
    return max(-1.0, min(1.0, dot / (left_norm * right_norm)))


def _verify_live_sources(refactoring_map: dict[str, Any], paths: set[str],
                        repo_root: Path) -> None:
    root = Path(os.path.abspath(os.fspath(repo_root)))
    file_hashes = {
        row["path"]: row.get("contentSha256")
        for row in refactoring_map.get("files", [])
        if isinstance(row, dict) and isinstance(row.get("path"), str)
    }
    for artifact in sorted(paths):
        candidate = Path(os.path.abspath(os.fspath(root / artifact)))
        try:
            candidate.relative_to(root)
        except ValueError as exc:
            raise ValueError(f"source path escapes repository root: {artifact}") from exc
        if not candidate.is_file():
            raise ValueError(f"current source is unavailable for edge endpoint {artifact}")
        actual = hashlib.sha256(candidate.read_bytes()).hexdigest()
        if actual != file_hashes.get(artifact):
            raise ValueError(f"current source digest differs from map for edge endpoint {artifact}")


def build_cosine_edge_attention_packet(
    refactoring_map: dict[str, Any], embedding_packet: dict[str, Any], *,
    inverse_temperature: float = 1.0, repo_root: Path = _REPOSITORY_ROOT,
) -> dict[str, Any]:
    """Score every typed local dependency witness from verified source vectors."""
    if not isinstance(embedding_packet, dict):
        raise ValueError("embedding packet must be a JSON object")
    if refactoring_map.get("schema") != MAP_SCHEMA:
        raise ValueError("unsupported refactoring-map schema")
    snapshot = refactoring_map.get("sourceSnapshot") or {}
    if snapshot.get("worktreeConsistentDuringScan") is not True:
        raise ValueError("refusing an inconsistent source snapshot")
    snapshot_sha = snapshot.get("pathContentManifestSha256")
    if (not isinstance(snapshot_sha, str) or len(snapshot_sha) != 64
            or any(character not in "0123456789abcdef" for character in snapshot_sha)):
        raise ValueError("source snapshot must have a lowercase SHA-256 digest")
    if (isinstance(inverse_temperature, bool)
            or not isinstance(inverse_temperature, (int, float))
            or not math.isfinite(inverse_temperature) or inverse_temperature <= 0):
        raise ValueError("inverse_temperature must be finite and positive")

    rebuilt = build_encoder_embedding_packet(
        refactoring_map, embedding_packet.get("encoderVersion"),
        embedding_packet.get("embeddings"),
        encoder_training=embedding_packet.get("encoderTraining"),
    )
    if embedding_packet != rebuilt:
        raise ValueError("embedding packet digest or normalized contents do not match map")
    embeddings = {
        row["artifactId"]: row["vector"] for row in embedding_packet["embeddings"]
    }
    vertices = {
        row["path"] for row in refactoring_map.get("files", [])
        if isinstance(row, dict) and isinstance(row.get("path"), str)
    }
    edges = []
    for edge in refactoring_map.get("dependencyEdges", []):
        if (not isinstance(edge, dict) or edge.get("kind") not in DEPENDENCY_KINDS
                or edge.get("from") not in vertices or edge.get("to") not in vertices):
            continue
        edges.append(edge)
    refs = [edge_reference(edge) for edge in edges]
    if len(refs) != len(set(refs)):
        raise ValueError("local dependency edges contain duplicate edge witnesses")
    missing = sorted({endpoint for edge in edges for endpoint in (edge["from"], edge["to"])
                      if endpoint not in embeddings})
    if missing:
        raise ValueError(
            "embedding packet lacks endpoints for complete local-edge scoring: "
            + ", ".join(missing[:5])
        )
    _verify_live_sources(
        refactoring_map,
        {endpoint for edge in edges for endpoint in (edge["from"], edge["to"])},
        repo_root,
    )
    scored = [{
        "edgeRef": edge_reference(edge),
        "logit": _cosine(embeddings[edge["from"]], embeddings[edge["to"]]),
    } for edge in edges]
    scored.sort(key=lambda row: row["edgeRef"])
    return {
        "schema": SCORE_SCHEMA,
        "sourceSnapshotSha256": snapshot_sha,
        "modelVersion": MODEL_VERSION,
        "featureVersion": f"cosine_of_{embedding_packet['encoderVersion']}",
        "edgeKinds": sorted(DEPENDENCY_KINDS),
        "encoderPacketSha256": embedding_packet["packetSha256"],
        "scoreMethod": "cosine_similarity_between_observed_edge_endpoints",
        "trainingStatus": "deterministic_untrained_baseline",
        "inverseTemperature": float(inverse_temperature),
        "edges": scored,
        "authority": (
            "source-bound embedding affinity over observed typed dependency witnesses; "
            "not causal importance, semantic equivalence, or trained attention"
        ),
    }


def _sparse_feature_cosine(left: dict[str, int], right: dict[str, int]) -> float:
    """Cosine for nonnegative sparse InfoTree feature-count maps."""
    left_scale = max(left.values(), default=0)
    right_scale = max(right.values(), default=0)
    if left_scale == 0 or right_scale == 0:
        return 0.0
    left_unit = {key: value / left_scale for key, value in left.items()}
    right_unit = {key: value / right_scale for key, value in right.items()}
    dot = math.fsum(left_unit[key] * right_unit[key]
                    for key in left_unit.keys() & right_unit.keys())
    left_norm = math.sqrt(math.fsum(value * value for value in left_unit.values()))
    right_norm = math.sqrt(math.fsum(value * value for value in right_unit.values()))
    return max(0.0, min(1.0, dot / (left_norm * right_norm)))


def build_infotree_dna_edge_attention_packet(
    refactoring_map: dict[str, Any], dna_records: list[dict[str, Any]],
    generation_manifest: dict[str, Any], *, inverse_temperature: float = 1.0,
    repo_root: Path = _REPOSITORY_ROOT,
) -> dict[str, Any]:
    """Score Lean import witnesses by cosine of verified current InfoTree DNA."""
    if refactoring_map.get("schema") != MAP_SCHEMA:
        raise ValueError("unsupported refactoring-map schema")
    snapshot = refactoring_map.get("sourceSnapshot") or {}
    if snapshot.get("worktreeConsistentDuringScan") is not True:
        raise ValueError("refusing an inconsistent source snapshot")
    snapshot_sha = snapshot.get("pathContentManifestSha256")
    if (not isinstance(snapshot_sha, str) or len(snapshot_sha) != 64
            or any(character not in "0123456789abcdef" for character in snapshot_sha)):
        raise ValueError("source snapshot must have a lowercase SHA-256 digest")
    if (isinstance(inverse_temperature, bool)
            or not isinstance(inverse_temperature, (int, float))
            or not math.isfinite(inverse_temperature) or inverse_temperature <= 0):
        raise ValueError("inverse_temperature must be finite and positive")
    validate_current_source_generation_manifest(
        refactoring_map, dna_records, generation_manifest,
    )
    if generation_manifest.get("sourceSnapshotSha256") != snapshot_sha:
        raise ValueError("InfoTree generation manifest belongs to another source snapshot")
    dna_by_path = {row["artifactId"]: row for row in dna_records}
    vertices = {
        row["path"] for row in refactoring_map.get("files", [])
        if isinstance(row, dict) and isinstance(row.get("path"), str)
    }
    edges = [
        edge for edge in refactoring_map.get("dependencyEdges", [])
        if isinstance(edge, dict) and edge.get("kind") == "lean_source_import"
        and edge.get("from") in vertices and edge.get("to") in vertices
    ]
    refs = [edge_reference(edge) for edge in edges]
    if len(refs) != len(set(refs)):
        raise ValueError("Lean import graph contains duplicate edge witnesses")
    endpoint_paths = {endpoint for edge in edges for endpoint in (edge["from"], edge["to"])}
    missing = sorted(endpoint_paths - set(dna_by_path))
    if missing:
        raise ValueError("InfoTree DNA is missing Lean import endpoints: " + ", ".join(missing[:5]))
    _verify_live_sources(refactoring_map, endpoint_paths, repo_root)
    incomplete = sorted(path for path in endpoint_paths
                        if dna_by_path[path].get("status") != "structural_dna_candidate"
                        or dna_by_path[path].get("captureLossless") is not True
                        or dna_by_path[path].get("leakageRowCount") != 0)
    if incomplete:
        raise ValueError("InfoTree DNA endpoint capture is partial or lossy: "
                         + ", ".join(incomplete[:5]))
    scores = []
    for edge in edges:
        source = dna_by_path[edge["from"]]
        target = dna_by_path[edge["to"]]
        scores.append({
            "edgeRef": edge_reference(edge),
            "logit": _sparse_feature_cosine(source["features"], target["features"]),
            "sourceDnaFingerprint": source["dnaFingerprint"],
            "targetDnaFingerprint": target["dnaFingerprint"],
        })
    scores.sort(key=lambda row: row["edgeRef"])
    return {
        "schema": SCORE_SCHEMA,
        "sourceSnapshotSha256": snapshot_sha,
        "generationId": generation_manifest["sourceGenerationId"],
        "generationManifestSha256": generation_manifest["manifestSha256"],
        "modelVersion": "infotree_dna_cosine_affinity_baseline.v1",
        "featureVersion": generation_manifest["infotreeFeatureVersion"],
        "edgeKinds": ["lean_source_import"],
        "scoreMethod": "cosine_similarity_between_verified_infotree_feature_counts",
        "trainingStatus": "deterministic_untrained_baseline",
        "inverseTemperature": float(inverse_temperature),
        "edges": scores,
        "authority": (
            "lossless current-source InfoTree structural affinity over observed Lean imports; "
            "not causal importance, semantic equivalence, or trained attention"
        ),
    }


def build_factorized_dna_edge_attention_packet(
    refactoring_map: dict[str, Any], embedding_packet: dict[str, Any],
    dna_records: list[dict[str, Any]], generation_manifest: dict[str, Any], *,
    source_affinity_weight: float = 0.5,
    infotree_dna_weight: float = 0.5,
    inverse_temperature: float = 1.0,
    repo_root: Path = _REPOSITORY_ROOT,
) -> dict[str, Any]:
    """Fuse source-code and compiler-DNA affinities on verified Lean imports.

    The weighted affinity is a log-linear energy: the downstream Gibbs
    distribution is proportional to the product of the two expert factors.
    Commit-lineage evidence is deliberately excluded because it describes
    historical attribution, not semantic compatibility of an import edge.
    """
    weights = (source_affinity_weight, infotree_dna_weight)
    if any(isinstance(weight, bool) or not isinstance(weight, (int, float))
           or not math.isfinite(weight) or weight < 0 for weight in weights):
        raise ValueError("factor weights must be finite nonnegative numbers")
    if not math.isclose(sum(weights), 1.0, rel_tol=0.0, abs_tol=1e-12):
        raise ValueError("factor weights must sum to one")
    if (isinstance(inverse_temperature, bool)
            or not isinstance(inverse_temperature, (int, float))
            or not math.isfinite(inverse_temperature) or inverse_temperature <= 0):
        raise ValueError("inverse_temperature must be finite and positive")

    dna_packet = build_infotree_dna_edge_attention_packet(
        refactoring_map, dna_records, generation_manifest,
        inverse_temperature=inverse_temperature, repo_root=repo_root,
    )
    rebuilt = build_encoder_embedding_packet(
        refactoring_map, embedding_packet.get("encoderVersion"),
        embedding_packet.get("embeddings"),
        encoder_training=embedding_packet.get("encoderTraining"),
    )
    if embedding_packet != rebuilt:
        raise ValueError("encoder packet digest or normalized contents do not match map")
    embeddings = {
        row["artifactId"]: row["vector"] for row in embedding_packet["embeddings"]
    }
    dna_by_ref = {row["edgeRef"]: row for row in dna_packet["edges"]}
    lean_edges = [
        edge for edge in refactoring_map.get("dependencyEdges", [])
        if isinstance(edge, dict) and edge.get("kind") == "lean_source_import"
    ]
    endpoint_paths = {path for edge in lean_edges for path in (edge.get("from"), edge.get("to"))}
    missing = sorted(path for path in endpoint_paths if path not in embeddings)
    if missing:
        raise ValueError("source embedding packet lacks Lean import endpoints: "
                         + ", ".join(missing[:5]))
    _verify_live_sources(refactoring_map, endpoint_paths, repo_root)

    scored = []
    for edge in lean_edges:
        ref = edge_reference(edge)
        dna_score = dna_by_ref.get(ref)
        if dna_score is None:
            raise ValueError("InfoTree DNA score packet does not cover every Lean import witness")
        raw_code_cosine = _cosine(embeddings[edge["from"]], embeddings[edge["to"]])
        # Put both channels on [0, 1] before combining their log-linear
        # energies; retain the signed cosine for audit and interpretation.
        code_affinity = (raw_code_cosine + 1.0) / 2.0
        dna_affinity = dna_score["logit"]
        scored.append({
            "edgeRef": ref,
            "logit": (source_affinity_weight * code_affinity
                      + infotree_dna_weight * dna_affinity),
            "scoreComponents": {
                "sourceEmbeddingCosine": raw_code_cosine,
                "sourceEmbeddingAffinity01": code_affinity,
                "infotreeDnaCosine": dna_affinity,
            },
            "factorWeights": {
                "sourceEmbeddingAffinity01": float(source_affinity_weight),
                "infotreeDnaCosine": float(infotree_dna_weight),
            },
            "sourceDnaFingerprint": dna_score["sourceDnaFingerprint"],
            "targetDnaFingerprint": dna_score["targetDnaFingerprint"],
        })
    scored.sort(key=lambda row: row["edgeRef"])
    return {
        "schema": SCORE_SCHEMA,
        "sourceSnapshotSha256": dna_packet["sourceSnapshotSha256"],
        "generationId": dna_packet["generationId"],
        "generationManifestSha256": dna_packet["generationManifestSha256"],
        "encoderPacketSha256": embedding_packet["packetSha256"],
        "modelVersion": "factorized_source_infotree_dna_affinity.v1",
        "featureVersion": f"{embedding_packet['encoderVersion']}+{dna_packet['featureVersion']}",
        "edgeKinds": ["lean_source_import"],
        "scoreMethod": "weighted_log_linear_product_of_source_and_infotree_affinity_factors",
        "factorWeights": {
            "sourceEmbeddingAffinity01": float(source_affinity_weight),
            "infotreeDnaCosine": float(infotree_dna_weight),
        },
        "trainingStatus": "deterministic_untrained_factorized_baseline",
        "inverseTemperature": float(inverse_temperature),
        "edges": scored,
        "authority": (
            "snapshot-bound source and lossless InfoTree structural affinities over observed "
            "Lean imports; not causal importance, semantic equivalence, or trained attention"
        ),
    }
def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("refactoring_map", type=Path)
    parser.add_argument("embedding_packet", type=Path, nargs="?")
    parser.add_argument("--infotree-dna", type=Path)
    parser.add_argument("--generation-manifest", type=Path)
    parser.add_argument("--fuse-infotree-dna", action="store_true",
                        help="fuse source embeddings and InfoTree DNA on Lean imports")
    parser.add_argument("--source-affinity-weight", type=float, default=0.5)
    parser.add_argument("--infotree-dna-weight", type=float, default=0.5)
    parser.add_argument("--repo-root", type=Path, default=_REPOSITORY_ROOT)
    parser.add_argument("--inverse-temperature", type=float, default=1.0)
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()
    refactoring_map = _read_json(args.refactoring_map)
    if args.fuse_infotree_dna:
        if (not args.embedding_packet or not args.infotree_dna
                or not args.generation_manifest):
            parser.error("fusion mode requires embedding_packet, --infotree-dna, "
                         "and --generation-manifest")
        packet = build_factorized_dna_edge_attention_packet(
            refactoring_map, _read_json(args.embedding_packet),
            _read_jsonl(args.infotree_dna), _read_json(args.generation_manifest),
            source_affinity_weight=args.source_affinity_weight,
            infotree_dna_weight=args.infotree_dna_weight,
            inverse_temperature=args.inverse_temperature,
            repo_root=args.repo_root,
        )
    elif args.infotree_dna or args.generation_manifest:
        if args.embedding_packet or not args.infotree_dna or not args.generation_manifest:
            parser.error("InfoTree mode requires --infotree-dna and --generation-manifest only")
        packet = build_infotree_dna_edge_attention_packet(
            refactoring_map, _read_jsonl(args.infotree_dna),
            _read_json(args.generation_manifest),
            inverse_temperature=args.inverse_temperature,
            repo_root=args.repo_root,
        )
    else:
        if not args.embedding_packet:
            parser.error("source-embedding mode requires an embedding_packet argument")
        packet = build_cosine_edge_attention_packet(
            refactoring_map, _read_json(args.embedding_packet),
            inverse_temperature=args.inverse_temperature,
            repo_root=args.repo_root,
        )
    args.out.parent.mkdir(parents=True, exist_ok=True)
    rendered = json.dumps(packet, sort_keys=True, ensure_ascii=False) + "\n"
    if args.out.suffix == ".gz":
        with gzip.open(args.out, "wt", encoding="utf-8") as stream:
            stream.write(rendered)
    else:
        args.out.write_text(rendered, encoding="utf-8")
    print(json.dumps({
        "schema": packet["schema"], "modelVersion": packet["modelVersion"],
        "scoredEdgeCount": len(packet["edges"]),
        "scoreMethod": packet["scoreMethod"],
        "edgeKinds": packet.get("edgeKinds", sorted(DEPENDENCY_KINDS)),
        "out": str(args.out),
    }, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
