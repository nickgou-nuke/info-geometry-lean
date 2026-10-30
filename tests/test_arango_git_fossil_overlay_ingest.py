from __future__ import annotations

import hashlib
import json
from pathlib import Path

import pytest

from tools.infra.arango_git_fossil_overlay_ingest import (
    _evolution_commit_file_key,
    _evolution_path_key,
    _iter_declaration_line_edges,
    _iter_evolution_commit_edges,
    _iter_node_line_edges,
    _iter_path_events,
    _prepare_evolution_reuse,
    build_stage_plan,
)


def _write_json(path: Path, value: dict) -> None:
    path.write_text(json.dumps(value, sort_keys=True), encoding="utf-8")


def _write_jsonl(path: Path, rows: list[dict]) -> str:
    payload = "".join(json.dumps(row, sort_keys=True) + "\n" for row in rows)
    path.write_text(payload, encoding="utf-8")
    return hashlib.sha256(payload.encode("utf-8")).hexdigest()


def _fixture(tmp_path: Path) -> tuple[Path, Path, Path]:
    overlay = tmp_path / "overlay"
    overlay.mkdir()
    git_head = "b" * 40
    generation_id = "a" * 64
    source = "lean/Sample.lean"
    source_sha = "c" * 64
    context_sha = "d" * 64
    path_fossil_id = hashlib.sha256(f"{git_head}\0{source}".encode()).hexdigest()
    event = {
        "schema": "info_geometry.git_path_fossil_event.v1",
        "historyRevision": git_head,
        "artifactPath": source,
        "commitSha": "e" * 40,
        "changeType": "M",
        "changedPath": source,
    }
    event_path = tmp_path / "events.jsonl"
    event_sha = _write_jsonl(event_path, [event])
    link = {
        "schema": "info_geometry.infotree_node_git_fossil_link.v1",
        "generationId": generation_id,
        "historyRevision": git_head,
        "currentSourcePath": source,
        "sourceSha256": source_sha,
        "leanContextFingerprint": context_sha,
        "rawCaptureSha256": "f" * 64,
        "rootKey": "root-1",
        "nodeKey": "node-1",
        "pathFossilId": path_fossil_id,
        "sourceSpan": {"startByte": 0, "endByte": 4, "startLine": 1, "endLineExclusive": 2},
        "lineFossilSpanIds": ["9" * 64],
        "lineFossilStatus": "linked",
        "fossilEventCount": 1,
        "pathHistoryStatus": "path_continuity_candidate_not_content_identity",
    }
    links_sha = _write_jsonl(overlay / "node_fossil_links.jsonl", [link])
    line_fossil_sha = _write_jsonl(overlay / "source_line_fossils.jsonl", [{
        "schema": "info_geometry.git_line_fossil_span.v1",
        "generationId": generation_id,
        "historyRevision": git_head,
        "lineFossilSpanId": "9" * 64,
        "sourcePath": source,
        "sourceSha256": source_sha,
        "startLine": 1,
        "endLineExclusive": 2,
        "originStartLine": 1,
        "originEndLine": 2,
        "lineCount": 1,
        "commitSha": "8" * 40,
        "originPath": source,
        "originStatus": "committed_line_origin",
    }])
    declaration_links_sha = _write_jsonl(
        overlay / "declaration_line_fossil_links.jsonl", [{
            "schema": "info_geometry.declaration_line_fossil_link.v1",
            "generationId": generation_id,
            "historyRevision": git_head,
            "currentSourcePath": source,
            "sourceSha256": source_sha,
            "rootKey": "root-1",
            "nodeKey": "node-1",
            "linkKey": "decl-link-1",
            "declKey": "d_" + "7" * 40,
            "declName": "Sample.sample",
            "lineFossilSpanIds": ["9" * 64],
            "relation": "current_declaration_line_origin_overlap",
            "authority": "test current declaration/source overlap",
        }],
    )
    lineage_features = {source: {
        "schema": "info_geometry.source_lineage_features.v1",
        "generationId": generation_id,
        "historyRevision": git_head,
        "sourcePath": source,
        "sourceSha256": source_sha,
        "lineAttributionStatus": "complete",
        "lineCount": 1,
        "attributedLineCount": 1,
        "committedLineCount": 1,
        "currentContentLineCount": 0,
        "distinctCommitCount": 1,
        "distinctOriginPathCount": 1,
        "declarationLinkCount": 1,
        "declarationWithLineOriginCount": 1,
        "distinctDeclarationCount": 1,
    }}
    lineage_sha = hashlib.sha256(json.dumps(
        lineage_features, sort_keys=True, ensure_ascii=False, separators=(",", ":")
    ).encode()).hexdigest()
    _write_json(overlay / "metadata.json", {
        "schema": "info_geometry.git_fossil_overlay_manifest.v1",
        "generationId": generation_id,
        "gitHead": git_head,
        "gitPathEventsSha256": event_sha,
        "nodeLinksSha256": links_sha,
        "sourceLineFossilsSha256": line_fossil_sha,
        "sourceLineFossilSpanCount": 1,
        "declarationLineFossilLinksSha256": declaration_links_sha,
        "declarationLineFossilLinkCount": 1,
        "declarationLineFossilEdgeCount": 1,
        "sourceLineageFeaturesByPath": lineage_features,
        "sourceLineageFeaturesSha256": lineage_sha,
        "nodeLinkCount": 1,
        "sourceCount": 1,
        "gitPathEventCount": 1,
    })
    raw_report_path = tmp_path / "raw-generation.json"
    _write_json(raw_report_path, {
        "generation_id": "raw-generation-1",
        "build_fingerprint": "build-fingerprint",
        "dry_run": False,
        "validation": {"ok": True},
        "preflight": {"source_provenance": [{
            "sourcePath": source,
            "sourceSha256": source_sha,
            "leanContextFingerprint": context_sha,
        }]},
    })
    return overlay, event_path, raw_report_path


def test_build_stage_plan_binds_events_nodes_and_raw_source_provenance(tmp_path: Path):
    overlay, events, raw_report = _fixture(tmp_path)

    plan = build_stage_plan(overlay, events, raw_report)

    assert plan["sourceCount"] == 1
    assert plan["nodeLinkCount"] == 1
    assert plan["pathEventCount"] == 1
    assert plan["sourceLineFossilSpanCount"] == 1
    line_edges = list(_iter_node_line_edges(plan))
    assert len(line_edges) == 1
    assert line_edges[0]["_from"].endswith("/node-1")
    assert line_edges[0]["_to"].endswith("/" + "9" * 64)
    declaration_edges = list(_iter_declaration_line_edges(plan))
    assert len(declaration_edges) == 1
    assert declaration_edges[0]["_from"].endswith("/decl-link-1")
    assert declaration_edges[0]["_to"].endswith("/" + "9" * 64)
    assert plan["collections"]["raw_nodes"] == "raw_infotree_nodes_g_raw-generation-1"
    assert plan["overlayGenerationId"] == "a" * 64
    assert plan["generationId"] != plan["overlayGenerationId"]
    assert plan["collections"]["path_events"].endswith(plan["generationId"])
    assert plan["collections"]["node_edges"].startswith(
        "repo_infotree_path_fossil_edges_g_"
    )


def test_build_stage_plan_rejects_node_link_from_another_generation(tmp_path: Path):
    overlay, events, raw_report = _fixture(tmp_path)
    links_path = overlay / "node_fossil_links.jsonl"
    link = json.loads(links_path.read_text(encoding="utf-8"))
    link["generationId"] = "9" * 64
    links_sha = _write_jsonl(links_path, [link])
    manifest_path = overlay / "metadata.json"
    manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
    manifest["nodeLinksSha256"] = links_sha
    _write_json(manifest_path, manifest)

    with pytest.raises(ValueError, match="different overlay generation"):
        build_stage_plan(overlay, events, raw_report)


def test_build_stage_plan_rejects_raw_source_provenance_mismatch(tmp_path: Path):
    overlay, events, raw_report = _fixture(tmp_path)
    report = json.loads(raw_report.read_text(encoding="utf-8"))
    report["preflight"]["source_provenance"][0]["sourceSha256"] = "0" * 64
    _write_json(raw_report, report)

    with pytest.raises(ValueError, match="provenance differs"):
        build_stage_plan(overlay, events, raw_report)


def test_build_stage_plan_rejects_event_hash_mismatch(tmp_path: Path):
    overlay, events, raw_report = _fixture(tmp_path)
    events.write_text("{}\n", encoding="utf-8")

    with pytest.raises(ValueError, match="event stream hash"):
        build_stage_plan(overlay, events, raw_report)


def test_build_stage_plan_rejects_source_line_fossil_hash_mismatch(tmp_path: Path):
    overlay, events, raw_report = _fixture(tmp_path)
    with (overlay / "source_line_fossils.jsonl").open("a", encoding="utf-8") as stream:
        stream.write("{}\n")

    with pytest.raises(ValueError, match="source line fossil file hash"):
        build_stage_plan(overlay, events, raw_report)


def test_build_stage_plan_recomputes_lineage_counts_from_shared_fossils(tmp_path: Path):
    overlay, events, raw_report = _fixture(tmp_path)
    manifest_path = overlay / "metadata.json"
    manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
    features = manifest["sourceLineageFeaturesByPath"]
    features["lean/Sample.lean"]["distinctCommitCount"] = 7
    manifest["sourceLineageFeaturesSha256"] = hashlib.sha256(json.dumps(
        features, sort_keys=True, ensure_ascii=False, separators=(",", ":")
    ).encode()).hexdigest()
    _write_json(manifest_path, manifest)

    with pytest.raises(ValueError, match="counts disagree with fossil streams"):
        build_stage_plan(overlay, events, raw_report)


def test_exact_evolution_edges_replace_duplicate_event_docs(monkeypatch, tmp_path: Path):
    overlay, events, raw_report = _fixture(tmp_path)
    plan = build_stage_plan(overlay, events, raw_report)
    event = json.loads(events.read_text(encoding="utf-8"))
    expected_edge = _evolution_commit_file_key(event)

    def fake_aql(_target, query, bind_vars):
        if "FOR row IN @rows" in query:
            row = bind_vars["rows"][0]
            assert row == {
                "edgeKey": expected_edge,
                "commitSha": event["commitSha"],
                "pathKey": _evolution_path_key(event["changedPath"]),
                "changeType": event["changeType"],
                "oldPath": None,
            }
            return [expected_edge]
        if "FOR c IN evo_commits" in query:
            return [plan["gitHead"]]
        raise AssertionError(f"unexpected AQL query: {query}")

    monkeypatch.setattr(
        "tools.infra.arango_git_fossil_overlay_ingest._aql", fake_aql
    )
    summary = _prepare_evolution_reuse(
        plan, object(), {"evo_commit_files", "evo_files", "evo_commits"}
    )

    assert summary["status"] == "exact_reuse"
    assert summary["reusedPathEvents"] == 1
    assert summary["overlayFallbackEvents"] == 0
    assert summary["snapshotHeadPresentInArango"] is True
    assert list(_iter_path_events(plan)) == []
    reuse_edges = list(_iter_evolution_commit_edges(plan))
    assert len(reuse_edges) == 1
    assert reuse_edges[0]["_to"] == f"evo_commits/{event['commitSha']}"
    assert reuse_edges[0]["evolutionCommitFileEdgeKey"] == expected_edge


@pytest.mark.parametrize("batch_size", [1, 500])
def test_conflicting_rename_sources_never_share_a_reused_base_edge(monkeypatch, tmp_path, batch_size):
    overlay, events, raw_report = _fixture(tmp_path)
    plan = build_stage_plan(overlay, events, raw_report)
    event = json.loads(events.read_text())
    rows = [{**event, "changeType": "R", "oldPath": old}
            for old in ("lean/BeforeA.lean", "lean/BeforeB.lean")]
    _write_jsonl(events, rows)
    plan["pathEventCount"] = 2

    def fake_aql(_target, query, bind_vars):
        if "FOR row IN @rows" in query:
            assert "edge.old_path == row.oldPath" in query
            assert "edge.old_path_base64 == null" in query
            # Even if either candidate is independently reported as matched,
            # one shared base key cannot stand for both rename origins.
            return [row["edgeKey"] for row in bind_vars["rows"]]
        return [plan["gitHead"]]

    monkeypatch.setattr("tools.infra.arango_git_fossil_overlay_ingest._aql", fake_aql)
    summary = _prepare_evolution_reuse(
        plan, object(), {"evo_commit_files", "evo_files", "evo_commits"}, batch_size=batch_size)
    assert summary["reusedPathEvents"] == 0
    assert summary["overlayFallbackEvents"] == 2
    assert {row["oldPath"] for row in _iter_path_events(plan)} == {
        "lean/BeforeA.lean", "lean/BeforeB.lean"}


def test_unmatched_evolution_edge_is_preserved_as_fallback(monkeypatch, tmp_path: Path):
    overlay, events, raw_report = _fixture(tmp_path)
    plan = build_stage_plan(overlay, events, raw_report)
    def fake_aql(_target, query, _bind_vars):
        if "FOR row IN @rows" in query:
            return []
        if "FOR c IN evo_commits" in query:
            return []
        raise AssertionError(f"unexpected AQL query: {query}")

    monkeypatch.setattr(
        "tools.infra.arango_git_fossil_overlay_ingest._aql", fake_aql
    )
    summary = _prepare_evolution_reuse(
        plan, object(), {"evo_commit_files", "evo_files", "evo_commits"}
    )

    assert summary["reusedPathEvents"] == 0
    assert summary["overlayFallbackEvents"] == 1
    fallback = list(_iter_path_events(plan))
    assert len(fallback) == 1
    assert fallback[0]["fallbackReason"] == "no_exact_commit_file_edge"
    assert len(list(_iter_evolution_commit_edges(plan))) == 0


def test_missing_evolution_collections_keeps_all_events_locally(tmp_path: Path):
    overlay, events, raw_report = _fixture(tmp_path)
    plan = build_stage_plan(overlay, events, raw_report)

    summary = _prepare_evolution_reuse(plan, object(), set())

    assert summary["baseCollectionsAvailable"] is False
    assert summary["overlayFallbackEvents"] == 1
    assert summary["fallbackReasonCounts"] == {
        "evolution_collections_unavailable": 1
    }
    assert len(list(_iter_path_events(plan))) == 1
    assert list(_iter_evolution_commit_edges(plan)) == []
