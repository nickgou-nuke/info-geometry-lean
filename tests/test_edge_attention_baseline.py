from __future__ import annotations

import gzip
import hashlib
import json
import math
import sys

import pytest

from tools.repository_evolution.attention_scc import build_attention_scc_overlay
from tools.repository_evolution.edge_attention_baseline import (
    build_cosine_edge_attention_packet,
    build_factorized_dna_edge_attention_packet,
    build_infotree_dna_edge_attention_packet,
    main as edge_attention_main,
)
from tools.repository_evolution.generation_manifest import (
    _canonical_sha256,
    build_current_source_generation_manifest,
)
from tools.repository_evolution.infotree_dna import FEATURE_VERSION, capture_bundle_fingerprint
from tools.repository_evolution.latent_taxonomy import build_encoder_embedding_packet


def _fixture(tmp_path):
    sources = {name: f"source {name}\n" for name in ("a", "b", "c")}
    for name, source in sources.items():
        (tmp_path / name).write_text(source, encoding="utf-8")
    edges = [
        {"from": "a", "to": "b", "kind": "python_import", "status": "observed"},
        {"from": "a", "to": "c", "kind": "python_import", "status": "observed"},
    ]
    report = {
        "schema": "info_geometry.refactoring_map.v1",
        "sourceSnapshot": {
            "worktreeConsistentDuringScan": True,
            "pathContentManifestSha256": "a" * 64,
        },
        "files": [{"path": name, "contentSha256": hashlib.sha256(
            sources[name].encode()).hexdigest()} for name in sources],
        "dependencyEdges": edges,
    }
    embeddings = [
        {"artifactId": "a", "sourceSha256": report["files"][0]["contentSha256"],
         "vector": [1.0, 0.0]},
        {"artifactId": "b", "sourceSha256": report["files"][1]["contentSha256"],
         "vector": [1.0, 0.0]},
        {"artifactId": "c", "sourceSha256": report["files"][2]["contentSha256"],
         "vector": [0.0, 1.0]},
    ]
    packet = build_encoder_embedding_packet(
        report, "test-encoder.v1", embeddings,
        encoder_training={"method": "fixture", "dataScope": "deterministic_no_training"},
    )
    return report, packet


def test_cosine_baseline_emits_complete_snapshot_bound_edge_scores(tmp_path):
    report, embeddings = _fixture(tmp_path)
    packet = build_cosine_edge_attention_packet(report, embeddings, repo_root=tmp_path)
    scores = {row["edgeRef"]: row["logit"] for row in packet["edges"]}

    assert packet["sourceSnapshotSha256"] == "a" * 64
    assert packet["trainingStatus"] == "deterministic_untrained_baseline"
    assert sorted(scores.values()) == [0.0, 1.0]
    overlay = build_attention_scc_overlay(report, packet, {"kind": "top_k", "k": 1})
    assert overlay["selectedEdgeCount"] == 1
    assert next(row for row in overlay["allEdgeFactors"] if row["selected"])["to"] == "b"


def test_cosine_baseline_requires_all_scored_edge_endpoints(tmp_path):
    report, embeddings = _fixture(tmp_path)
    embeddings["embeddings"] = embeddings["embeddings"][:-1]
    embeddings = build_encoder_embedding_packet(
        report, embeddings["encoderVersion"], embeddings["embeddings"],
        encoder_training=embeddings["encoderTraining"],
    )
    with pytest.raises(ValueError, match="lacks endpoints"):
        build_cosine_edge_attention_packet(report, embeddings, repo_root=tmp_path)


@pytest.mark.parametrize("temperature", [0.0, -1.0, math.inf, math.nan, True])
def test_cosine_baseline_rejects_invalid_inverse_temperature(temperature, tmp_path):
    report, embeddings = _fixture(tmp_path)
    with pytest.raises(ValueError, match="finite and positive"):
        build_cosine_edge_attention_packet(
            report, embeddings, inverse_temperature=temperature, repo_root=tmp_path,
        )


def test_cosine_baseline_rejects_tampered_embedding_receipt(tmp_path):
    report, embeddings = _fixture(tmp_path)
    embeddings["embeddings"][0]["vector"][0] = 0.5
    with pytest.raises(ValueError, match="digest or normalized contents"):
        build_cosine_edge_attention_packet(report, embeddings, repo_root=tmp_path)


def test_cosine_baseline_rejects_sources_changed_after_embedding_capture(tmp_path):
    report, embeddings = _fixture(tmp_path)
    (tmp_path / "b").write_text("changed after embedding capture\n", encoding="utf-8")

    with pytest.raises(ValueError, match="current source digest differs"):
        build_cosine_edge_attention_packet(report, embeddings, repo_root=tmp_path)


def _infotree_fixture(tmp_path):
    source_paths = ("lean/A.lean", "lean/B.lean")
    for path in source_paths:
        target = tmp_path / path
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(path.encode())
    map_files = [{
        "path": path, "role": "lean_source", "module": path[5:-5],
        "contentSha256": hashlib.sha256(path.encode()).hexdigest(),
        "buildTargets": ["InfoGeometry"], "ownerStatus": "indexed",
    } for path in source_paths]
    source_map = {
        "schema": "info_geometry.refactoring_map.v1",
        "sourceSnapshot": {
            "gitHead": "a" * 40, "worktreeConsistentDuringScan": True,
            "pathContentManifestSha256": "b" * 64,
            "filesystemTopologySha256": "c" * 64,
        },
        "analysisProvenance": {
            "analysisInputsConsistentDuringScan": True,
            "scannerSourceSha256": "d" * 64,
            "lakeManifestSha256": "e" * 64,
        },
        "files": map_files,
        "dependencyEdges": [{
            "from": source_paths[0], "to": source_paths[1],
            "kind": "lean_source_import", "status": "observed",
        }, {
            "from": source_paths[0], "to": source_paths[1],
            "kind": "python_import", "status": "observed",
        }],
    }
    records = []
    for index, path in enumerate(source_paths):
        source_sha = map_files[index]["contentSha256"]
        features = {"node.kind=tactic": index + 1, "node.depth_bucket=2-4": 2}
        row_hashes = {
            "raw_infotree_roots.jsonl": str(index + 2) * 64,
            "raw_infotree_nodes.jsonl": str(index + 1) * 64,
            "raw_infotree_projection_leakage.jsonl": str(index + 4) * 64,
        }
        raw_capture = capture_bundle_fingerprint(row_hashes)
        context = str(index + 3) * 64
        records.append({
            "schema": "info_geometry.infotree_structural_dna.v1",
            "featureVersion": FEATURE_VERSION,
            "artifactId": path,
            "sourceSha256": source_sha,
            "leanContextFingerprint": context,
            "exporterSourceSha256": "e" * 64,
            "rawRowFileSha256": row_hashes,
            "rawCaptureSha256": raw_capture,
            "features": features,
            "captureLossless": True,
            "leakageRowCount": 0,
            "status": "structural_dna_candidate",
            "dnaFingerprint": _canonical_sha256({
                "featureVersion": FEATURE_VERSION,
                "sourceSha256": source_sha,
                "leanContextFingerprint": context,
                "exporterSourceSha256": "e" * 64,
                "rawCaptureSha256": raw_capture,
                "features": features,
            }),
        })
    manifest = build_current_source_generation_manifest(source_map, records)
    return source_map, records, manifest


def test_infotree_dna_scores_lean_imports_and_binds_generation_receipt(tmp_path):
    source_map, records, manifest = _infotree_fixture(tmp_path)
    packet = build_infotree_dna_edge_attention_packet(
        source_map, records, manifest, repo_root=tmp_path,
    )

    assert packet["edgeKinds"] == ["lean_source_import"]
    assert packet["generationManifestSha256"] == manifest["manifestSha256"]
    assert packet["edges"][0]["logit"] == pytest.approx(6 / math.sqrt(40))
    assert packet["edges"][0]["sourceDnaFingerprint"] == records[0]["dnaFingerprint"]
    overlay = build_attention_scc_overlay(source_map, packet, {"kind": "top_k", "k": 1})
    assert overlay["edgeKinds"] == ["lean_source_import"]
    assert overlay["scorePacketProvenance"]["generationManifestSha256"] == manifest["manifestSha256"]
    assert overlay["allEdgeFactors"][0]["targetDnaFingerprint"] == records[1]["dnaFingerprint"]
    assert overlay["observedDependencyEdgeCount"] == 1


def test_factorized_source_and_infotree_attention_retains_each_factor(tmp_path):
    source_map, records, manifest = _infotree_fixture(tmp_path)
    embeddings = build_encoder_embedding_packet(
        source_map, "fixture-code-encoder.v1", [
            {"artifactId": "lean/A.lean",
             "sourceSha256": records[0]["sourceSha256"], "vector": [1.0, 0.0]},
            {"artifactId": "lean/B.lean",
             "sourceSha256": records[1]["sourceSha256"], "vector": [0.0, 1.0]},
        ], encoder_training={
            "method": "deterministic_fixture", "dataScope": "deterministic_no_training",
        },
    )

    packet = build_factorized_dna_edge_attention_packet(
        source_map, embeddings, records, manifest,
        source_affinity_weight=0.25, infotree_dna_weight=0.75,
        repo_root=tmp_path,
    )

    row = packet["edges"][0]
    assert packet["modelVersion"] == "factorized_source_infotree_dna_affinity.v1"
    assert packet["edgeKinds"] == ["lean_source_import"]
    assert packet["trainingStatus"] == "deterministic_untrained_factorized_baseline"
    assert packet["encoderPacketSha256"] == embeddings["packetSha256"]
    assert row["scoreComponents"]["sourceEmbeddingCosine"] == pytest.approx(0.0)
    assert row["scoreComponents"]["sourceEmbeddingAffinity01"] == pytest.approx(0.5)
    assert row["scoreComponents"]["infotreeDnaCosine"] == pytest.approx(6 / math.sqrt(40))
    assert row["logit"] == pytest.approx(0.25 * 0.5 + 0.75 * (6 / math.sqrt(40)))
    assert row["factorWeights"] == {
        "sourceEmbeddingAffinity01": 0.25,
        "infotreeDnaCosine": 0.75,
    }

    overlay = build_attention_scc_overlay(source_map, packet, {"kind": "top_k", "k": 1})
    factor = overlay["allEdgeFactors"][0]
    assert factor["scoreComponents"] == row["scoreComponents"]
    assert factor["factorWeights"] == row["factorWeights"]
    assert overlay["scorePacketProvenance"]["encoderPacketSha256"] == embeddings["packetSha256"]
    assert overlay["scorePacketProvenance"]["factorWeights"] == row["factorWeights"]


@pytest.mark.parametrize("weights", [(0.0, 0.0), (0.3, 0.3), (-0.1, 1.1), (True, 0.0)])
def test_factorized_attention_rejects_invalid_factor_weights(tmp_path, weights):
    source_map, records, manifest = _infotree_fixture(tmp_path)
    embeddings = build_encoder_embedding_packet(
        source_map, "fixture-code-encoder.v1", [
            {"artifactId": "lean/A.lean", "sourceSha256": records[0]["sourceSha256"],
             "vector": [1.0, 0.0]},
            {"artifactId": "lean/B.lean", "sourceSha256": records[1]["sourceSha256"],
             "vector": [0.0, 1.0]},
        ], encoder_training={
            "method": "deterministic_fixture", "dataScope": "deterministic_no_training",
        },
    )
    with pytest.raises(ValueError, match="factor weights"):
        build_factorized_dna_edge_attention_packet(
            source_map, embeddings, records, manifest,
            source_affinity_weight=weights[0], infotree_dna_weight=weights[1],
            repo_root=tmp_path,
        )


def test_infotree_dna_attention_rejects_lossy_edge_endpoint(tmp_path):
    source_map, records, manifest = _infotree_fixture(tmp_path)
    records[1]["captureLossless"] = False
    records[1]["leakageRowCount"] = 1
    records[1]["status"] = "partial_structural_candidate_with_recorded_loss"
    manifest = build_current_source_generation_manifest(source_map, records)

    with pytest.raises(ValueError, match="partial or lossy"):
        build_infotree_dna_edge_attention_packet(
            source_map, records, manifest, repo_root=tmp_path,
        )


def test_infotree_dna_attention_rejects_tampered_generation_manifest(tmp_path):
    source_map, records, manifest = _infotree_fixture(tmp_path)
    manifest["coverageRatio"] = 0.5

    with pytest.raises(ValueError, match="manifest does not match"):
        build_infotree_dna_edge_attention_packet(
            source_map, records, manifest, repo_root=tmp_path,
        )


def test_source_embedding_cli_writes_a_readable_gzip_score_packet(tmp_path, monkeypatch):
    report, embeddings = _fixture(tmp_path)
    map_path = tmp_path / "map.json"
    embeddings_path = tmp_path / "embeddings.json"
    output_path = tmp_path / "scores.json.gz"
    map_path.write_text(json.dumps(report), encoding="utf-8")
    embeddings_path.write_text(json.dumps(embeddings), encoding="utf-8")
    monkeypatch.setattr(sys, "argv", [
        "edge_attention_baseline.py", str(map_path), str(embeddings_path),
        "--repo-root", str(tmp_path), "--out", str(output_path),
    ])

    assert edge_attention_main() == 0
    with gzip.open(output_path, "rt", encoding="utf-8") as stream:
        packet = json.load(stream)
    assert packet["modelVersion"] == "endpoint_cosine_affinity_baseline.v1"
    assert len(packet["edges"]) == 2


def test_infotree_cli_writes_typed_generation_bound_scores(tmp_path, monkeypatch):
    source_map, records, manifest = _infotree_fixture(tmp_path)
    map_path = tmp_path / "map.json"
    dna_path = tmp_path / "dna.jsonl"
    manifest_path = tmp_path / "manifest.json"
    output_path = tmp_path / "lean-scores.json"
    map_path.write_text(json.dumps(source_map), encoding="utf-8")
    dna_path.write_text("".join(json.dumps(row) + "\n" for row in records),
                        encoding="utf-8")
    manifest_path.write_text(json.dumps(manifest), encoding="utf-8")
    monkeypatch.setattr(sys, "argv", [
        "edge_attention_baseline.py", str(map_path), "--infotree-dna", str(dna_path),
        "--generation-manifest", str(manifest_path), "--out", str(output_path),
        "--repo-root", str(tmp_path),
    ])

    assert edge_attention_main() == 0
    packet = json.loads(output_path.read_text(encoding="utf-8"))
    assert packet["edgeKinds"] == ["lean_source_import"]
    assert packet["generationId"] == manifest["sourceGenerationId"]
