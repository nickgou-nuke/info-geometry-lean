#!/usr/bin/env python3
"""Build source-bound lexical-hashing embeddings as a non-neural baseline.

The token hashing implementation is reused from the existing OpenClaw Lean
indexer. These vectors are navigation/classification features, not
transformer embeddings or semantic evidence.
"""
from __future__ import annotations

import argparse
import gzip
import hashlib
import json
import sys
from pathlib import Path
from typing import Any

_REPOSITORY_ROOT = Path(__file__).resolve().parents[2]
if str(_REPOSITORY_ROOT) not in sys.path:
    sys.path.insert(0, str(_REPOSITORY_ROOT))
_SOURCE_ROOT = _REPOSITORY_ROOT / "src"
if str(_SOURCE_ROOT) not in sys.path:
    sys.path.insert(0, str(_SOURCE_ROOT))

from tools.infra.openclaw_lean_brain_ingest import hash_embedding
from tools.repository_evolution.latent_taxonomy import build_encoder_embedding_packet
from tools.repository_evolution.refactoring_map import ROOT, SOURCE_SUFFIXES


def _read_json(path: Path) -> dict[str, Any]:
    opener = gzip.open if path.suffix == ".gz" else open
    with opener(path, "rt", encoding="utf-8") as stream:
        value = json.load(stream)
    if not isinstance(value, dict):
        raise ValueError(f"{path}: expected a JSON object")
    return value


def build_source_hash_packet(report: dict[str, Any], repo_root: Path = ROOT, *,
                             dimension: int = 384) -> dict[str, Any]:
    """Hash current code source using the repository's existing tokenizer.

    Only files with source-language suffixes enter the packet. Other map
    artifacts remain in the taxonomy output and abstain from an encoder model
    when no source vector is available.
    """
    if isinstance(dimension, bool) or not isinstance(dimension, int) or dimension < 1:
        raise ValueError("dimension must be a positive integer")
    if report.get("schema") != "info_geometry.refactoring_map.v1":
        raise ValueError("unsupported refactoring-map schema")
    snapshot = report.get("sourceSnapshot") or {}
    if snapshot.get("worktreeConsistentDuringScan") is not True:
        raise ValueError("refusing a mixed or inconsistent source snapshot")
    root = repo_root.resolve()
    embeddings = []
    for row in report.get("files", []):
        if not isinstance(row, dict) or not isinstance(row.get("path"), str):
            continue
        artifact = row["path"]
        if Path(artifact).suffix.lower() not in SOURCE_SUFFIXES:
            continue
        if not isinstance(row.get("contentSha256"), str):
            # External and unreadable rows may lack a current-worktree content
            # digest; retain them in the map and abstain from encoder scoring.
            continue
        source_path = (root / artifact).resolve()
        try:
            source_path.relative_to(root)
        except ValueError as exc:
            raise ValueError(f"source path escapes repository root: {artifact}") from exc
        raw = source_path.read_bytes()
        actual_sha = hashlib.sha256(raw).hexdigest()
        if actual_sha != row.get("contentSha256"):
            raise ValueError(f"current source digest differs from map for {artifact}")
        try:
            source_text = raw.decode("utf-8")
        except UnicodeDecodeError as exc:
            raise ValueError(f"code source is not UTF-8: {artifact}") from exc
        embeddings.append({
            "artifactId": artifact,
            "sourceSha256": actual_sha,
            "vector": hash_embedding(source_text, dim=dimension),
        })
    if not embeddings:
        raise ValueError("refactoring map contains no readable code-source files")
    encoder_version = f"feature_hashing_v1_dim_{dimension}"
    return build_encoder_embedding_packet(
        report, encoder_version, embeddings,
        encoder_training={"method": "existing_openclaw_feature_hashing_v1",
                         "dataScope": "deterministic_no_training"},
    )


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("refactoring_map", type=Path)
    parser.add_argument("--repo-root", type=Path, default=ROOT)
    parser.add_argument("--embedding-dim", type=int, default=384)
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()
    report = _read_json(args.refactoring_map)
    packet = build_source_hash_packet(report, args.repo_root, dimension=args.embedding_dim)
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(packet, sort_keys=True, ensure_ascii=False) + "\n",
                        encoding="utf-8")
    print(json.dumps({
        "schema": packet["schema"],
        "encoderVersion": packet["encoderVersion"],
        "embeddingDimension": packet["embeddingDimension"],
        "embeddedArtifactCount": len(packet["embeddings"]),
        "packetSha256": packet["packetSha256"],
        "out": str(args.out),
    }, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
