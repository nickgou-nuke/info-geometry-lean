from __future__ import annotations

import copy
from collections import Counter
import math
import subprocess
import sys
from pathlib import Path

import pytest

from tools.repository_evolution.latent_taxonomy import (
    FEATURE_VERSION,
    MODEL_SCHEMA,
    _features_for_map,
    apply_latent_expert_model,
    build_encoder_embedding_packet,
)


def test_documented_script_path_entrypoint_loads_its_repository_imports():
    repository_root = Path(__file__).resolve().parents[1]
    script = repository_root / "tools/repository_evolution/latent_taxonomy.py"

    result = subprocess.run(
        [sys.executable, str(script), "--help"],
        cwd=repository_root,
        check=False,
        capture_output=True,
        text=True,
    )

    assert result.returncode == 0, result.stderr
    assert "refactoring_map" in result.stdout


def test_structural_features_encode_typed_directional_two_hop_motifs():
    report = {
        "files": [{"path": path, "sizeBytes": 10} for path in "abcd"],
        "dependencyEdges": [
            {"from": "a", "to": "b", "kind": "lean_source_import"},
            {"from": "b", "to": "c", "kind": "python_import"},
            {"from": "a", "to": "d", "kind": "lean_source_import"},
            {"from": "d", "to": "c", "kind": "python_import"},
        ],
        "leanDeclarationCandidates": [],
    }

    vectors, evidence = _features_for_map(report)

    assert vectors["a"][
        "dependency.walk2=out:lean_source_import>out:python_import"
    ] == pytest.approx(math.log(3))
    assert vectors["c"][
        "dependency.walk2=in:python_import>in:lean_source_import"
    ] == pytest.approx(math.log(3))
    assert any(row["kind"] == "dependency_edge" for row in evidence["a"])


def test_aggregated_walks_match_enumeration_with_loops_parallel_edges_and_boundaries():
    paths = ["a", "b", "c"]
    edges = [
        {"from": "a", "to": "b", "kind": "import"},
        {"from": "a", "to": "b", "kind": "import"},
        {"from": "b", "to": "b", "kind": "reference"},
        {"from": "c", "to": "b", "kind": "reference"},
        {"from": "b", "to": "outside", "kind": "import"},
        {"from": "outside", "to": "a", "kind": "reference"},
    ]
    adjacency = {path: [] for path in paths}
    for edge in edges:
        if edge["from"] in adjacency:
            adjacency[edge["from"]].append((edge["to"], "out", edge["kind"]))
        if edge["to"] in adjacency:
            adjacency[edge["to"]].append((edge["from"], "in", edge["kind"]))
    vectors, _ = _features_for_map({
        "files": [{"path": path} for path in paths],
        "dependencyEdges": edges, "leanDeclarationCandidates": [],
    })
    for path in paths:
        expected = Counter()
        for middle, direction, kind in adjacency[path]:
            for _, next_direction, next_kind in adjacency.get(middle, []):
                expected[f"dependency.walk2={direction}:{kind}>{next_direction}:{next_kind}"] += 1
        actual = {key: value for key, value in vectors[path].items()
                  if key.startswith("dependency.walk2=")}
        assert actual == {key: math.log1p(count) for key, count in expected.items()}


def test_walk_features_scale_to_a_large_hub_without_materializing_walks():
    leaves = [f"leaf{i}" for i in range(10000)]
    vectors, _ = _features_for_map({
        "files": [{"path": path} for path in ["hub", *leaves]],
        "dependencyEdges": [{"from": path, "to": "hub", "kind": "import"}
                            for path in leaves],
        "leanDeclarationCandidates": [],
    })
    # Each leaf reaches every leaf through the hub, including itself.
    for path in leaves:
        assert vectors[path]["dependency.walk2=out:import>in:import"] == math.log1p(len(leaves))
    assert vectors["hub"]["dependency.walk2=in:import>out:import"] == math.log1p(len(leaves))


def test_verified_debruijn_fingerprints_enter_taxonomy_features_with_provenance():
    report = {
        "files": [{"path": "lean/A.lean", "sizeBytes": 20,
                   "compilerFingerprints": {
                       "declarationCount": 4,
                       "uniqueTypeDigestCount": 3,
                       "uniqueValueDigestCount": 4,
                       "openTypeDigestCount": 0,
                       "openValueDigestCount": 0,
                       "typeDigestAlgorithm": "lean-expr-debruijn-v4",
                   }}],
        "dependencyEdges": [],
        "leanDeclarationCandidates": [],
        "sourceSnapshot": {"worktreeConsistentDuringScan": True},
        "analysisProvenance": {"analysisInputsConsistentDuringScan": True},
        "compilerArtifactEvidence": {
            "joinStatus": "verified_fingerprint_rows_joined_by_source_file",
            "fingerprintIntegration": {
                "status": "source_olean_and_export_hashes_verified",
            },
        },
    }

    vectors, evidence = _features_for_map(report)

    assert FEATURE_VERSION == "repository_taxonomy_features.v4"
    assert vectors["lean/A.lean"]["compiler.type_digest_algorithm=lean-expr-debruijn-v4"] == 1
    assert vectors["lean/A.lean"]["compiler.unique_type_digest_count"] == 3
    assert vectors["lean/A.lean"]["compiler.type_digest_reuse_ratio"] == pytest.approx(0.25)
    assert any(row["kind"] == "compiler_type_fingerprint_summary"
               for row in evidence["lean/A.lean"])


def test_unverified_fingerprint_summary_is_rejected_by_taxonomy_features():
    report = {
        "files": [{"path": "lean/A.lean", "compilerFingerprints": {
            "declarationCount": 1,
            "uniqueTypeDigestCount": 1,
            "uniqueValueDigestCount": 1,
            "openTypeDigestCount": 0,
            "openValueDigestCount": 0,
            "typeDigestAlgorithm": "lean-expr-debruijn-v4",
        }}],
        "dependencyEdges": [],
        "leanDeclarationCandidates": [],
    }
    with pytest.raises(ValueError, match="not provenance-verified"):
        _features_for_map(report)


def test_verified_git_lineage_features_enter_the_current_artifact_taxonomy():
    import hashlib
    import json

    from tools.repository_evolution.git_fossil_overlay import _generation_id

    path = "lean/A.lean"
    source_sha = "a" * 64
    snapshot = {
        "gitHead": "1" * 40,
        "pathContentManifestSha256": "2" * 64,
        "filesystemTopologySha256": "3" * 64,
        "worktreeConsistentDuringScan": True,
    }
    provenance = {
        "scannerSourceSha256": "4" * 64,
        "lakeManifestSha256": "5" * 64,
        "analysisInputsConsistentDuringScan": True,
    }
    generation = _generation_id(snapshot, provenance)
    lineage = {
        "schema": "info_geometry.source_lineage_features.v1",
        "generationId": generation,
        "historyRevision": snapshot["gitHead"],
        "sourcePath": path,
        "sourceSha256": source_sha,
        "lineAttributionStatus": "complete",
        "lineCount": 4,
        "attributedLineCount": 4,
        "committedLineCount": 3,
        "currentContentLineCount": 1,
        "distinctCommitCount": 2,
        "distinctOriginPathCount": 1,
        "declarationLinkCount": 2,
        "declarationWithLineOriginCount": 1,
        "distinctDeclarationCount": 2,
    }
    lineage_by_path = {path: lineage}
    lineage_sha = hashlib.sha256(json.dumps(
        lineage_by_path, sort_keys=True, ensure_ascii=False, separators=(",", ":")
    ).encode()).hexdigest()
    report = {
        "files": [{"path": path, "role": "lean_source", "contentSha256": source_sha}],
        "dependencyEdges": [],
        "leanDeclarationCandidates": [],
        "sourceSnapshot": snapshot,
        "analysisProvenance": provenance,
    }
    dna = [{"artifactId": path, "sourceSha256": source_sha, "dnaFingerprint": "dna-a",
            "features": {}}]
    overlay = {
        "schema": "info_geometry.git_fossil_overlay_manifest.v1",
        "generationId": generation,
        "gitHead": snapshot["gitHead"],
        "pathContentManifestSha256": snapshot["pathContentManifestSha256"],
        "sourceLineageFeaturesByPath": lineage_by_path,
        "sourceLineageFeaturesSha256": lineage_sha,
    }

    vectors, evidence = _features_for_map(report, dna, overlay)

    assert vectors[path]["git.lineage.attribution_status=complete"] == 1
    assert vectors[path]["git.lineage.committedFraction=75-100%"] == 1
    assert vectors[path]["git.lineage.declarationAttributionFraction=50-75%"] == 1
    assert any(row["kind"] == "git_line_origin_summary" for row in evidence[path])


def test_git_lineage_features_reject_tampered_summary_digest():
    from tools.repository_evolution.git_fossil_overlay import _generation_id

    path = "lean/A.lean"
    snapshot = {"gitHead": "1" * 40, "pathContentManifestSha256": "2" * 64,
                "filesystemTopologySha256": "3" * 64, "worktreeConsistentDuringScan": True}
    provenance = {"scannerSourceSha256": "4" * 64, "lakeManifestSha256": "5" * 64,
                  "analysisInputsConsistentDuringScan": True}
    generation = _generation_id(snapshot, provenance)
    report = {"files": [{"path": path, "contentSha256": "a" * 64}],
              "dependencyEdges": [], "leanDeclarationCandidates": [],
              "sourceSnapshot": snapshot, "analysisProvenance": provenance}
    dna = [{"artifactId": path, "sourceSha256": "a" * 64, "features": {}}]
    overlay = {"schema": "info_geometry.git_fossil_overlay_manifest.v1",
               "generationId": generation, "gitHead": snapshot["gitHead"],
               "pathContentManifestSha256": snapshot["pathContentManifestSha256"],
               "sourceLineageFeaturesByPath": {path: {"sourceSha256": "a" * 64}},
               "sourceLineageFeaturesSha256": "0" * 64}
    with pytest.raises(ValueError, match="feature digest mismatch"):
        _features_for_map(report, dna, overlay)


def test_model_with_git_lineage_features_requires_the_generation_bound_overlay():
    report, model = _fixture()
    model["featureVocabulary"].append("git.lineage.lineCount_bucket=1-1023")
    with pytest.raises(ValueError, match="provide its generation-bound overlay"):
        apply_latent_expert_model(report, model)


def _fixture():
    report = {
        "schema": "info_geometry.refactoring_map.v1",
        "sourceSnapshot": {
            "worktreeConsistentDuringScan": True,
            "pathContentManifestSha256": "snapshot-a",
        },
        "files": [{"path": "lean/Alpha.lean", "role": "lean_source",
                   "ownerStatus": "certain", "buildTargets": ["Root"],
                   "sizeBytes": 1200, "contentSha256": "a" * 64}],
        "dependencyEdges": [{"from": "lean/Alpha.lean", "to": "lean/Beta.lean",
                             "kind": "lean_source_import"}],
        "leanDeclarationCandidates": [{"sourcePath": "lean/Alpha.lean", "kind": "theorem",
                                       "line": 4}],
    }
    model = {
        "schema": MODEL_SCHEMA,
        "modelVersion": "test-v1",
        "featureVersion": FEATURE_VERSION,
        "featureVocabulary": ["artifact.role=lean_source", "declaration.kind=theorem",
                              "dependency.out=lean_source_import"],
        "projection": [{"artifact.role=lean_source": 1.0,
                        "declaration.kind=theorem": 1.0,
                        "dependency.out=lean_source_import": 1.0}],
        "experts": [
            {"id": "proof_shape", "gateBias": 0,
             "evidenceKinds": ["lexical_declaration_candidate"],
             "gateWeights": [1.0],
             "labelHeadsByFacet": {
                 "artifact_role": {"proof_module": {"bias": 2.0, "weights": [1.0]},
                                   "other_role": {"bias": 0.0, "weights": [-1.0]}},
                 "semantic_archetype": {
                     "proof_owner": {"bias": 1.0, "weights": [0.5]},
                     "adapter": {"bias": 0.0, "weights": [-0.5]},
                 },
             }},
            {"id": "source_owner", "gateBias": 0,
             "evidenceKinds": ["build_ownership_candidate"],
             "gateWeights": [-1.0],
             "labelHeadsByFacet": {
                 "artifact_role": {"proof_module": {"bias": 0.0, "weights": [0.0]},
                                   "other_role": {"bias": 0.0, "weights": [0.0]}},
                 "semantic_archetype": {
                     "proof_owner": {"bias": 0.0, "weights": [0.0]},
                     "adapter": {"bias": 0.0, "weights": [0.0]},
                 },
             }},
        ],
        "minimumLabelProbability": 0.0,
        "minimumLabelMargin": 0.0,
    }
    return report, model


def test_projection_mixture_and_evidence_remain_unreviewed_proposals():
    report, model = _fixture()
    result = apply_latent_expert_model(report, model)
    artifact = result["artifacts"][0]
    assert result["projectionDimension"] == 1
    assert artifact["latentCoordinates"][0] > 0
    assert sum(artifact["expertGates"].values()) == pytest.approx(1.0)
    for proposals in artifact["combinedLabelProposalsByFacet"].values():
        assert all(0.0 <= item["probability"] <= 1.0 for item in proposals)
    assert artifact["combinedLabelProposalsByFacet"]["artifact_role"][0]["label"] == "proof_module"
    assert artifact["combinedLabelProposalsByFacet"]["semantic_archetype"][0]["label"] == "proof_owner"
    assert result["labelFacets"] == ["artifact_role", "semantic_archetype"]
    assert artifact["status"] == "unreviewed_taxonomy_proposal"
    assert artifact["expertProposals"][0]["evidence"]
    assert artifact["expertProposals"][0]["scoreSemantics"] == "uncalibrated_sigmoid_score"
    assert result["reviewedLabelCount"] == 0


def test_labels_within_a_facet_are_independent_not_softmax_competitors():
    report, model = _fixture()
    for expert in model["experts"]:
        expert["labelHeadsByFacet"]["artifact_role"] = {
            "formal_source": {"bias": 5.0, "weights": [0.0]},
            "analysis_tool": {"bias": 5.0, "weights": [0.0]},
        }
    result = apply_latent_expert_model(report, model)
    scores = result["artifacts"][0]["combinedLabelProposalsByFacet"]["artifact_role"]
    assert len(scores) == 2
    assert all(score["probability"] > 0.9 for score in scores)
    assert sum(score["probability"] for score in scores) > 1.8


def test_model_rejects_inconsistent_worktree_snapshot():
    report, model = _fixture()
    report["sourceSnapshot"]["worktreeConsistentDuringScan"] = False
    with pytest.raises(ValueError, match="inconsistent source snapshot"):
        apply_latent_expert_model(report, model)


def test_infotree_dna_must_match_the_exact_map_source_digest():
    report, model = _fixture()
    dna = [{"artifactId": "lean/Alpha.lean", "sourceSha256": "b" * 64,
            "features": {"node.kind= tactic": 4}, "dnaFingerprint": "fp"}]
    with pytest.raises(ValueError, match="source hash does not match"):
        apply_latent_expert_model(report, model, dna)


def test_encoder_embeddings_are_source_bound_and_projected_into_latent_coordinates():
    report, model = _fixture()
    embedding_rows = [{"artifactId": "lean/Alpha.lean", "sourceSha256": "a" * 64,
                       "vector": [0.5, 2.0]}]
    packet = build_encoder_embedding_packet(report, "tiny-code-encoder-v1", embedding_rows)
    structural = apply_latent_expert_model(report, model)
    model["encoderSpec"] = {"version": "tiny-code-encoder-v1", "dimension": 2}
    model["encoderProjection"] = [[2.0, 0.5]]

    encoded = apply_latent_expert_model(report, model, encoder_packet=packet)
    assert encoded["artifacts"][0]["latentCoordinates"][0] - structural["artifacts"][0][
        "latentCoordinates"
    ][0] == pytest.approx(2.0)
    assert encoded["encoderVersion"] == "tiny-code-encoder-v1"
    assert encoded["encoderEmbeddingPacketSha256"] == packet["packetSha256"]


def test_encoder_packet_rejects_stale_or_incomplete_artifact_vectors():
    report, _ = _fixture()
    stale = [{"artifactId": "lean/Alpha.lean", "sourceSha256": "b" * 64,
              "vector": [0.1]}]
    with pytest.raises(ValueError, match="source hash does not match"):
        build_encoder_embedding_packet(report, "tiny-code-encoder-v1", stale)
    with pytest.raises(ValueError, match="at least one current artifact vector"):
        build_encoder_embedding_packet(report, "tiny-code-encoder-v1", [])


def test_artifacts_without_encoder_vectors_abstain_individually():
    report, model = _fixture()
    report["files"].append({"path": "assets/logo.bin", "role": "non_source_asset",
                            "contentSha256": "b" * 64})
    packet = build_encoder_embedding_packet(report, "encoder-v1", [
        {"artifactId": "lean/Alpha.lean", "sourceSha256": "a" * 64,
         "vector": [0.25, -0.25]},
    ])
    model["encoderSpec"] = {"version": "encoder-v1", "dimension": 2}
    model["encoderProjection"] = [[1.0, 1.0]]
    result = apply_latent_expert_model(report, model, encoder_packet=packet)
    artifacts = {row["artifactId"]: row for row in result["artifacts"]}
    assert result["encoderCoverage"] == {
        "embeddedArtifactCount": 1, "targetArtifactCount": 2, "missingArtifactCount": 1
    }
    assert artifacts["assets/logo.bin"]["status"] == "abstain"
    assert artifacts["assets/logo.bin"]["abstainReasonsByFacet"]["artifact_role"] == [
        "encoder_embedding_missing"
    ]


def test_encoder_packet_must_match_the_model_encoder_spec():
    report, model = _fixture()
    packet = build_encoder_embedding_packet(report, "encoder-v1", [
        {"artifactId": "lean/Alpha.lean", "sourceSha256": "a" * 64,
         "vector": [0.25, -0.25]},
    ])
    model["encoderSpec"] = {"version": "encoder-v2", "dimension": 2}
    model["encoderProjection"] = [[1.0, 1.0]]
    with pytest.raises(ValueError, match="version does not match"):
        apply_latent_expert_model(report, model, encoder_packet=packet)


def test_encoder_packet_rejects_vector_tampering_after_fingerprinting():
    report, model = _fixture()
    packet = build_encoder_embedding_packet(report, "encoder-v1", [
        {"artifactId": "lean/Alpha.lean", "sourceSha256": "a" * 64,
         "vector": [0.25, -0.25]},
    ])
    model["encoderSpec"] = {"version": "encoder-v1", "dimension": 2}
    model["encoderProjection"] = [[1.0, 1.0]]
    packet["embeddings"][0]["vector"][0] = 999.0
    with pytest.raises(ValueError, match="digest or normalized contents"):
        apply_latent_expert_model(report, model, encoder_packet=packet)


def test_low_label_margin_abstains_instead_of_forcing_taxonomy():
    report, model = _fixture()
    model = copy.deepcopy(model)
    model["minimumLabelMargin"] = 1.0
    result = apply_latent_expert_model(report, model)
    assert result["artifacts"][0]["status"] == "abstain"
    assert "label_margin_below_threshold" in result["artifacts"][0]["abstainReasonsByFacet"][
        "artifact_role"
    ]


def test_experts_must_share_the_same_label_vocabulary_within_each_facet():
    report, model = _fixture()
    del model["experts"][1]["labelHeadsByFacet"]["artifact_role"]["other_role"]
    with pytest.raises(ValueError, match="share one non-empty label vocabulary for artifact_role"):
        apply_latent_expert_model(report, model)
