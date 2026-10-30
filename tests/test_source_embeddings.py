from __future__ import annotations

import hashlib
from pathlib import Path

import pytest

from tools.infra.openclaw_lean_brain_ingest import hash_embedding
from tools.repository_evolution.source_embeddings import build_source_hash_packet


def _map(root: Path):
    source = b"theorem alpha : True := True.intro\n"
    binary = b"\x00\xff\x01"
    (root / "lean").mkdir(parents=True)
    (root / "assets").mkdir()
    (root / "lean/Alpha.lean").write_bytes(source)
    (root / "assets/logo.bin").write_bytes(binary)
    return {
        "schema": "info_geometry.refactoring_map.v1",
        "sourceSnapshot": {"worktreeConsistentDuringScan": True,
                           "pathContentManifestSha256": "snapshot-a"},
        "files": [
            {"path": "lean/Alpha.lean",
             "contentSha256": hashlib.sha256(source).hexdigest()},
            {"path": "assets/logo.bin",
             "contentSha256": hashlib.sha256(binary).hexdigest()},
            {"path": "external_refs/Old.lean", "role": "external_reference"},
        ],
    }


def test_existing_feature_hash_encoder_builds_source_bound_partial_packet(tmp_path: Path):
    report = _map(tmp_path)
    packet = build_source_hash_packet(report, tmp_path, dimension=32)
    assert packet["encoderVersion"] == "feature_hashing_v1_dim_32"
    assert packet["embeddingDimension"] == 32
    assert [row["artifactId"] for row in packet["embeddings"]] == ["lean/Alpha.lean"]
    assert packet["embeddings"][0]["vector"] == hash_embedding(
        (tmp_path / "lean/Alpha.lean").read_text(), dim=32
    )
    assert packet["packetSha256"]


def test_source_hash_baseline_rejects_changed_source_and_bad_dimensions(tmp_path: Path):
    report = _map(tmp_path)
    (tmp_path / "lean/Alpha.lean").write_text("theorem changed : True := True.intro\n")
    with pytest.raises(ValueError, match="current source digest differs"):
        build_source_hash_packet(report, tmp_path)
    with pytest.raises(ValueError, match="positive integer"):
        build_source_hash_packet(report, tmp_path, dimension=0)
