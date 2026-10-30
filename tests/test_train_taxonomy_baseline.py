from __future__ import annotations

import hashlib
import json

import pytest

from tools.repository_evolution.latent_taxonomy import apply_latent_expert_model
from tools.repository_evolution.latent_taxonomy import build_encoder_embedding_packet
from tools.repository_evolution.generation_manifest import (
    _canonical_sha256,
    build_current_source_generation_manifest,
)
from tools.repository_evolution.infotree_dna import (
    FEATURE_VERSION,
    capture_bundle_fingerprint,
)
from tools.repository_evolution.train_taxonomy_baseline import train_taxonomy_baseline


SNAPSHOT_SHA = "a" * 64


def _fixtures():
    assignments = [
        ("train", "formal"), ("train", "formal"), ("train", "tooling"),
        ("train", "tooling"), ("validation", "formal"), ("validation", "tooling"),
        ("test", "formal"), ("test", "tooling"),
    ]
    files = []
    rows = []
    embedding_rows = []
    for index, (split, label) in enumerate(assignments):
        artifact = f"src/Module{index}.lean"
        source_hash = hashlib.sha256(f"source-{index}".encode()).hexdigest()
        files.append({"path": artifact, "contentSha256": source_hash,
                      "role": "lean_source"})
        rows.append({
            "schema": "info_geometry.reviewed_taxonomy_corpus.v4",
            "artifactId": artifact,
            "sourceSha256": source_hash,
            "splitGroup": f"module:Module{index}",
            "split": split,
            "labels": {"artifact_role": [label]},
            "labelDefinitionsByFacet": {"artifact_role": {
                label: f"A reviewed {label} codebase artifact"
            }},
            "labelSetCompleteByFacet": {"artifact_role": True},
            "consensusByFacet": {"artifact_role": {
                "reviewerIds": ["reviewer-1", "reviewer-2"],
                "independentReviewerCount": 2,
                "method": "unanimous_exact_label_set",
            }},
            "provenance": {
                "sourceSnapshotSha256": SNAPSHOT_SHA,
                "scannerSourceSha256": "b" * 64,
                "lakeManifestSha256": "c" * 64,
                "labelAuthority": "human_adjudicated",
            },
        })
        sign = 1.0 if label == "formal" else -1.0
        embedding_rows.append({
            "artifactId": artifact,
            "sourceSha256": source_hash,
            "vector": [sign * (1.0 + index / 100), sign * 0.2, 0.0],
        })
    corpus_bytes = b"".join(
        (json.dumps(row, sort_keys=True, ensure_ascii=False) + "\n").encode()
        for row in rows
    )
    corpus = {
        "schema": "info_geometry.reviewed_taxonomy_corpus_manifest.v4",
        "corpusSchema": "info_geometry.reviewed_taxonomy_corpus.v4",
        "sourceSnapshotSha256": SNAPSHOT_SHA,
        "scannerSourceSha256": "b" * 64,
        "lakeManifestSha256": "c" * 64,
        "artifactCount": len(rows),
        "splitCounts": {"train": 4, "validation": 2, "test": 2},
        "corpusRowsSha256": hashlib.sha256(corpus_bytes).hexdigest(),
        "labelCodebookSchema": "info_geometry.taxonomy_label_codebook.v1",
        "labelCodebook": [
            {"facet": "artifact_role", "label": label,
             "definition": f"A reviewed {label} codebase artifact"}
            for label in ("formal", "tooling")
        ],
        "rows": rows,
    }
    codebook_payload = {"schema": "info_geometry.taxonomy_label_codebook.v1",
                        "labels": corpus["labelCodebook"]}
    corpus["labelCodebookSha256"] = hashlib.sha256(json.dumps(
        codebook_payload, sort_keys=True, ensure_ascii=False, separators=(",", ":")
    ).encode()).hexdigest()
    report = {
        "schema": "info_geometry.refactoring_map.v1",
        "sourceSnapshot": {"gitHead": "9" * 40,
                           "worktreeConsistentDuringScan": True,
                           "pathContentManifestSha256": SNAPSHOT_SHA,
                           "filesystemTopologySha256": "f" * 64},
        "analysisProvenance": {"analysisInputsConsistentDuringScan": True,
                               "scannerSourceSha256": "b" * 64,
                               "lakeManifestSha256": "c" * 64},
        "files": files,
        "dependencyEdges": [],
        "leanDeclarationCandidates": [],
    }
    packet = build_encoder_embedding_packet(
        report, "test-encoder.v1", embedding_rows,
        encoder_training={"method": "test_fixture_encoder", "dataScope": "external_pretrained"},
    )
    return report, corpus, packet


def _infotree_records(report):
    records = []
    for index, row in enumerate(report["files"][:4]):
        features = {"node.kind=tactic": 2 + index}
        context = hashlib.sha256(f"context-{index}".encode()).hexdigest()
        row_hashes = {
            "raw_infotree_roots.jsonl": str(index + 1) * 64,
            "raw_infotree_nodes.jsonl": str(index + 2) * 64,
            "raw_infotree_projection_leakage.jsonl": str(index + 3) * 64,
        }
        raw_capture = capture_bundle_fingerprint(row_hashes)
        records.append({
            "schema": "info_geometry.infotree_structural_dna.v1",
            "featureVersion": FEATURE_VERSION,
            "artifactId": row["path"],
            "sourceSha256": row["contentSha256"],
            "leanContextFingerprint": context,
            "exporterSourceSha256": "e" * 64,
            "rawRowFileSha256": row_hashes,
            "rawCaptureSha256": raw_capture,
            "features": features,
            "captureLossless": False,
            "leakageRowCount": 1,
            "status": "partial_structural_candidate_with_recorded_loss",
            "dnaFingerprint": _canonical_sha256({
                "featureVersion": FEATURE_VERSION,
                "sourceSha256": row["contentSha256"],
                "leanContextFingerprint": context,
                "exporterSourceSha256": "e" * 64,
                "rawCaptureSha256": raw_capture,
                "features": features,
            }),
        })
    return records


def test_reviewed_baseline_trainer_fits_pca_multilabel_heads_and_evaluates_holdouts():
    report, corpus, packet = _fixtures()
    model, training_report = train_taxonomy_baseline(
        report, corpus, packet, latent_dimension=2, l2=0.1, max_iterations=4000,
    )
    assert model["schema"] == "info_geometry.latent_expert_model.v3"
    assert model["featureVocabulary"] == []
    assert model["trainingMethod"] == (
        "train_only_multiview_pca_balanced_l2_ovr_logistic_with_oof_router.v5")
    assert training_report["test"]["microF1At05AcrossFacets"] == pytest.approx(1.0)
    assert set(training_report["viewAblations"]) == {
        "sourceOnly", "structureOnly", "sourceAndStructure",
        "sourceAndStructureWithoutGitLineage", "comparisonPolicy", "testSetPolicy",
    }
    assert training_report["viewAblations"]["sourceOnly"]["test"] is not None
    assert training_report["viewAblations"]["structureOnly"]["status"] == (
        "not_available_no_reviewed_train_graph_features")
    proposals = apply_latent_expert_model(report, model, encoder_packet=packet)
    by_artifact = {row["artifactId"]: row for row in proposals["artifacts"]}
    formal = by_artifact["src/Module0.lean"]["combinedLabelProposalsByFacet"]["artifact_role"]
    tooling = by_artifact["src/Module2.lean"]["combinedLabelProposalsByFacet"]["artifact_role"]
    assert formal[0]["label"] == "formal"
    assert tooling[0]["label"] == "tooling"


def test_trainer_fuses_typed_graph_declarations_and_source_bound_infotree_without_paths_or_git():
    report, corpus, packet = _fixtures()
    report["dependencyEdges"] = []
    for index in range(4):
        for _ in range(1 if index < 2 else 3):
            report["dependencyEdges"].append({
                "from": f"src/Module{index}.lean", "to": "src/Shared.lean",
                "kind": "lean_source_import",
            })
    report["dependencyEdges"].extend([
        {"from": "src/Module0.lean", "to": "src/Module1.lean", "kind": "test_import"},
        {"from": "src/Module0.lean", "to": "src/Module1.lean", "kind": "git_commit_parent"},
    ])
    report["leanDeclarationCandidates"] = [
        {"sourcePath": f"src/Module{index}.lean",
         "kind": "theorem" if index < 2 else "definition", "line": 1}
        for index in range(4)
    ]
    report["files"][0]["gitPathHistory"] = {
        "touchCount": 100, "changeTypes": {"M": 50}
    }
    dna = _infotree_records(report)
    module4_sha = next(row["contentSha256"] for row in report["files"]
                       if row["path"] == "src/Module4.lean")
    batch_reports = [{
        "schema": "info_geometry.raw_infotree_batch_export_report.v1",
        "results": [{
            "file": "src/Module4.lean", "status": "ok",
            "source_provenance": {"sourceSha256": module4_sha,
                                  "leanContextFingerprint": "capture-context"},
        }],
    }]
    rejection_reports = [{
        "schema": "info_geometry.infotree_dna_rejection_report.v1",
        "rejectionCount": 1,
        "rejections": [{
            "artifactId": "src/Module4.lean", "reason": "stale_lean_context",
            "reportedSourceSha256": module4_sha,
        }],
    }]
    dna_manifest = build_current_source_generation_manifest(
        report, dna, batch_reports=batch_reports, rejection_reports=rejection_reports
    )
    model, training_report = train_taxonomy_baseline(
        report, corpus, packet, latent_dimension=3, max_iterations=4000,
        infotree_dna=dna, infotree_dna_manifest=dna_manifest,
        infotree_batch_reports=batch_reports,
        infotree_dna_rejection_reports=rejection_reports,
    )
    assert "dependency.out=lean_source_import" in model["featureVocabulary"]
    assert "declaration.kind=theorem" in model["featureVocabulary"]
    assert "infotree.node.kind=tactic" in model["featureVocabulary"]
    assert not any("test_import" in name or "git_commit_parent" in name
                   for name in model["featureVocabulary"])
    assert not any(name.startswith(("git.", "artifact.role=", "artifact.ownerStatus="))
                   for name in model["featureVocabulary"])
    audit = training_report["trainingInfoTreeCaptureAudit"]
    assert audit["trainingArtifactRecords"] == 4
    assert audit["partialCaptureCount"] == 4
    assert audit["leakageRowCount"] == 4
    assert training_report["trainingInfoTreeGenerationAudit"]["status"] == (
        "partial_missing_captures")
    assert training_report["trainingInfoTreeGenerationAudit"]["manifestScope"][
        "kind"] == "full_current_lean_inventory"
    assert training_report["trainingInfoTreeGenerationAudit"]["missingLeanSources"] == [
        "src/Module4.lean", "src/Module5.lean", "src/Module6.lean", "src/Module7.lean",
    ]
    assert training_report["trainingInfoTreeGenerationAudit"][
        "lakeOwnerStatusCounts"] == {"not_recorded": 8}
    assert training_report["trainingInfoTreeGenerationAudit"][
        "lakeBuildTargetCaptureCoverage"]["sourcesWithoutBuildTargets"] == {
            "expectedSourceCount": 8,
            "capturedSourceCount": 4,
            "missingSourceCount": 4,
        }
    assert training_report["trainingInfoTreeGenerationAudit"]["unindexedLeanSources"] == []
    assert training_report["trainingInfoTreeGenerationAudit"]["unreachableLeanModules"] == []
    capture_audit = training_report["trainingInfoTreeGenerationAudit"][
        "captureAttemptAudit"]
    assert capture_audit["missingSourceDiagnostics"][0]["reason"] == (
        "lean_context_rejected")
    assert len(model["trainingInfoTreeCaptureSha256"]) == 64
    assert model["trainingInfoTreeCaptureSha256"] == training_report[
        "trainingInfoTreeCaptureSha256"]
    assert len(model["trainingStructuralInputsSha256"]) == 64
    proposals = apply_latent_expert_model(report, model, dna, packet)
    assert proposals["artifacts"][0]["latentCoordinates"]
    assert [expert["id"] for expert in model["experts"]] == [
        "source_embedding", "dependency_infotree", "source_structure_fused",
    ]
    assert model["router"]["learnsInputConditionalWeights"] is True
    assert model["router"]["method"] == (
        "train_only_specialist_loss_distillation_softmax.v1")
    assert training_report["routerTraining"]["optimizer"]["converged"] is True
    assert training_report["routerTraining"]["crossFit"]["status"] == (
        "grouped_out_of_fold")
    assert training_report["routerTraining"]["crossFit"]["groupIsolation"] is True
    assert training_report["routerTraining"]["targetLossSource"] == "grouped_out_of_fold"
    assert training_report["routedValidation"]["artifactCount"] == 2
    assert training_report["routedTest"]["artifactCount"] == 2
    assert set(proposals["artifacts"][0]["expertLatentCoordinates"]) == {
        "source_embedding", "dependency_infotree", "source_structure_fused",
    }
    assert set(proposals["artifacts"][0]["expertGates"]) == {
        "source_embedding", "dependency_infotree", "source_structure_fused",
    }
    formal_gates = proposals["artifacts"][0]["expertGates"]
    tooling_gates = proposals["artifacts"][2]["expertGates"]
    assert any(abs(formal_gates[key] - tooling_gates[key]) > 1e-8
               for key in formal_gates)


def test_trainer_uses_generation_bound_lineage_features_as_reviewed_taxonomy_inputs():
    report, corpus, packet = _fixtures()
    dna = _infotree_records(report)
    from tools.repository_evolution.git_fossil_overlay import _generation_id

    snapshot = report["sourceSnapshot"]
    provenance = report["analysisProvenance"]
    generation_id = _generation_id(snapshot, provenance)
    lineage_features = {}
    for index, record in enumerate(dna):
        path = record["artifactId"]
        lineage_features[path] = {
            "schema": "info_geometry.source_lineage_features.v1",
            "generationId": generation_id,
            "historyRevision": snapshot["gitHead"],
            "sourcePath": path,
            "sourceSha256": record["sourceSha256"],
            "lineAttributionStatus": "complete",
            "lineCount": 4,
            "attributedLineCount": 4,
            "committedLineCount": index + 1,
            "currentContentLineCount": 3 - index,
            "distinctCommitCount": 1,
            "distinctOriginPathCount": 1,
            "declarationLinkCount": 2,
            "declarationWithLineOriginCount": 1,
            "distinctDeclarationCount": 2,
        }
    lineage_sha = _canonical_sha256(lineage_features)
    overlay = {
        "schema": "info_geometry.git_fossil_overlay_manifest.v1",
        "generationId": generation_id,
        "gitHead": snapshot["gitHead"],
        "pathContentManifestSha256": snapshot["pathContentManifestSha256"],
        "sourceCount": len(dna),
        "gitPathEventsSha256": "1" * 64,
        "gitPathEventCount": 0,
        "nodeLinksSha256": "2" * 64,
        "nodeLinkCount": 0,
        "sourceLineFossilsSha256": "3" * 64,
        "sourceLineFossilSpanCount": 0,
        "declarationLineFossilLinksSha256": "4" * 64,
        "declarationLineFossilLinkCount": 0,
        "declarationLineFossilEdgeCount": 0,
        "sourceLineageFeaturesByPath": lineage_features,
        "sourceLineageFeaturesSha256": lineage_sha,
    }
    dna_manifest = build_current_source_generation_manifest(report, dna, overlay)

    model, training_report = train_taxonomy_baseline(
        report, corpus, packet, latent_dimension=3, max_iterations=4000,
        infotree_dna=dna, infotree_dna_manifest=dna_manifest,
        git_fossil_overlay_manifest=overlay,
    )

    assert any(name.startswith("git.lineage.") for name in model["featureVocabulary"])
    assert training_report["trainingInfoTreeGenerationAudit"][
        "gitLineageFeatureSourceCount"] == len(dna)
    lineage_ablation = training_report["viewAblations"][
        "sourceAndStructureWithoutGitLineage"]
    assert lineage_ablation["removedGitLineageFeatureCount"] > 0
    assert lineage_ablation["validation"] is not None
    assert lineage_ablation["test"] is not None
    proposals = apply_latent_expert_model(report, model, dna, packet, overlay)
    assert proposals["gitLineageFeatureGenerationId"] == generation_id
    assert proposals["gitLineageFeatureSourceCount"] == len(dna)


def test_structural_expert_remains_available_when_source_embedding_is_missing():
    report, corpus, packet = _fixtures()
    new_artifact = "src/Unreviewed.lean"
    report["files"].append({
        "path": new_artifact,
        "contentSha256": hashlib.sha256(b"unreviewed").hexdigest(),
        "role": "lean_source",
    })
    report["dependencyEdges"].append({
        "from": new_artifact, "to": "src/Module0.lean", "kind": "lean_source_import",
    })
    model, _ = train_taxonomy_baseline(report, corpus, packet, latent_dimension=2)
    proposals = apply_latent_expert_model(report, model, encoder_packet=packet)
    artifact = next(row for row in proposals["artifacts"]
                    if row["artifactId"] == new_artifact)
    assert set(artifact["expertGates"]) == {"dependency_infotree"}
    assert artifact["status"] != "abstain"


def test_trainer_rejects_rows_that_do_not_supply_independent_label_groups():
    report, corpus, packet = _fixtures()
    for row in corpus["rows"]:
        row["splitGroup"] = f"{row['split']}:{row['labels']['artifact_role'][0]}"
    corpus_bytes = b"".join(
        (json.dumps(row, sort_keys=True, ensure_ascii=False) + "\n").encode()
        for row in corpus["rows"]
    )
    corpus["corpusRowsSha256"] = hashlib.sha256(corpus_bytes).hexdigest()
    with pytest.raises(ValueError, match="labels_below_minimum_independent_training_groups"):
        train_taxonomy_baseline(report, corpus, packet, latent_dimension=2)


def test_trainer_rejects_stale_infotree_structure_features():
    report, corpus, packet = _fixtures()
    dna = _infotree_records(report)
    manifest = build_current_source_generation_manifest(report, dna)
    dna[0]["sourceSha256"] = "f" * 64
    with pytest.raises(ValueError, match="source digest differs"):
        train_taxonomy_baseline(report, corpus, packet, infotree_dna=dna,
                                infotree_dna_manifest=manifest)


def test_trainer_rejects_a_corpus_without_closed_world_label_sets():
    report, corpus, packet = _fixtures()
    corpus["rows"][0]["labelSetCompleteByFacet"]["artifact_role"] = False
    corpus_bytes = b"".join(
        (json.dumps(row, sort_keys=True, ensure_ascii=False) + "\n").encode()
        for row in corpus["rows"]
    )
    corpus["corpusRowsSha256"] = hashlib.sha256(corpus_bytes).hexdigest()
    with pytest.raises(ValueError, match="not trainable"):
        train_taxonomy_baseline(report, corpus, packet)


def test_trainer_rejects_rows_without_independent_reviewer_consensus():
    report, corpus, packet = _fixtures()
    corpus["rows"][0].pop("consensusByFacet")
    corpus["corpusRowsSha256"] = hashlib.sha256(b"".join(
        (json.dumps(row, sort_keys=True, ensure_ascii=False) + "\n").encode()
        for row in corpus["rows"]
    )).hexdigest()
    with pytest.raises(ValueError, match="insufficient_independent_review_consensus"):
        train_taxonomy_baseline(report, corpus, packet)


def test_trainer_refuses_changed_corpus_to_map_provenance():
    report, corpus, packet = _fixtures()
    corpus["scannerSourceSha256"] = "d" * 64
    with pytest.raises(ValueError, match="scanner provenance differs"):
        train_taxonomy_baseline(report, corpus, packet)


def test_trainer_rejects_encoder_pretraining_on_the_heldout_repository_source():
    report, corpus, packet = _fixtures()
    packet = build_encoder_embedding_packet(
        report, packet["encoderVersion"], packet["embeddings"],
        encoder_training={"method": "repo_masked_language_model",
                          "dataScope": "repository_all_source"},
    )
    with pytest.raises(ValueError, match="encoder saw held-out repository source"):
        train_taxonomy_baseline(report, corpus, packet)
