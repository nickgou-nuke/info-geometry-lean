from __future__ import annotations

import hashlib
import json
import subprocess
from pathlib import Path
from unittest.mock import patch

import pytest

from tools.repository_evolution.git_fossil_overlay import (
    _current_line_fossils,
    _node_source_span,
    _snapshot_scope_evidence,
    _source_relative,
    build_git_fossil_overlay,
)
from tools.repository_evolution.infotree_dna import extract_one


def _write_jsonl(path: Path, rows: list[dict]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("".join(json.dumps(row, sort_keys=True) + "\n" for row in rows))


def test_source_relative_preserves_lexical_symlink_path(tmp_path: Path):
    target = tmp_path / "external/Target.lean"
    target.parent.mkdir(parents=True)
    target.write_text("theorem target : True := True.intro\n")
    alias = tmp_path / "lean/TargetAlias.lean"
    alias.parent.mkdir(parents=True)
    try:
        alias.symlink_to("../external/Target.lean")
    except OSError as exc:
        pytest.skip(f"symlink creation unavailable: {exc}")

    assert _source_relative(tmp_path, alias) == "lean/TargetAlias.lean"


def test_current_line_fossils_attribute_committed_and_worktree_lines(tmp_path: Path):
    repo = tmp_path / "repo"
    repo.mkdir()

    def git(*args: str) -> str:
        return subprocess.run(
            ["git", "-C", str(repo), *args], check=True, capture_output=True, text=True
        ).stdout.strip()

    git("init", "-q")
    git("config", "user.email", "test@example.invalid")
    git("config", "user.name", "Test")
    source = repo / "Sample.lean"
    source.write_text("line one\nline two\nline three\n")
    git("add", "Sample.lean")
    git("commit", "-q", "-m", "initial")
    original_head = git("rev-parse", "HEAD")
    source.write_text("line one\nchanged line\nline three\n")

    spans, status = _current_line_fossils(
        repo, "Sample.lean", original_head, hashlib.sha256(source.read_bytes()).hexdigest()
    )

    assert status == "complete"
    assert len(spans) == 3
    assert spans[0]["commitSha"] == original_head
    assert spans[0]["startLine"] == 1 and spans[0]["endLineExclusive"] == 2
    assert spans[1]["commitSha"] == "0" * 40
    assert spans[1]["originStatus"] == "uncommitted_current_content"
    assert spans[2]["commitSha"] == original_head


def test_node_source_span_uses_utf8_byte_offsets_and_half_open_lines():
    source = "α\ntheorem x := True.intro\n".encode("utf-8")
    start = source.index(b"theorem")
    end = source.index(b"\n", start)
    span = _node_source_span({"startPos": start, "endPos": end}, source)
    assert span == {
        "startByte": start,
        "endByte": end,
        "startLine": 2,
        "endLineExclusive": 3,
    }


def test_scoped_snapshot_evidence_accepts_only_disjoint_reported_changes():
    snapshot = {
        "worktreeConsistentDuringScan": False,
        "changedPathCountDuringScan": 2,
        "changedPathSampleDuringScan": ["docs/active.md", "lean/Other.lean"],
    }
    evidence = _snapshot_scope_evidence(
        snapshot,
        {"lean/Sample.lean"},
        {"lean/Sample.lean"},
        selected_scope=True,
        allow_unrelated_changes=True,
    )
    assert evidence["status"] == "selected_scope_disjoint_from_observed_worktree_changes"
    assert evidence["worktreeConsistentDuringScan"] is False
    assert evidence["changedPathsDuringScan"] == ["docs/active.md", "lean/Other.lean"]


def test_scoped_snapshot_evidence_rejects_changed_target_or_incomplete_sample():
    with pytest.raises(ValueError, match="intersects paths changed"):
        _snapshot_scope_evidence(
            {"worktreeConsistentDuringScan": False,
             "changedPathCountDuringScan": 1,
             "changedPathSampleDuringScan": ["lean/Sample.lean"]},
            {"lean/Sample.lean"}, {"lean/Sample.lean"},
            selected_scope=True, allow_unrelated_changes=True,
        )
    with pytest.raises(ValueError, match="every changed path"):
        _snapshot_scope_evidence(
            {"worktreeConsistentDuringScan": False,
             "changedPathCountDuringScan": 2,
             "changedPathSampleDuringScan": ["docs/active.md"]},
            {"lean/Sample.lean"}, {"lean/Sample.lean"},
            selected_scope=True, allow_unrelated_changes=True,
        )


def test_scoped_snapshot_evidence_accepts_complete_changed_path_set_over_legacy_sample():
    changed_paths = [f"docs/churn-{index:02d}.md" for index in range(25)]
    digest = hashlib.sha256(json.dumps(
        changed_paths, ensure_ascii=False, separators=(",", ":")
    ).encode("utf-8")).hexdigest()
    evidence = _snapshot_scope_evidence(
        {
            "worktreeConsistentDuringScan": False,
            "changedPathCountDuringScan": len(changed_paths),
            "changedPathSampleDuringScan": changed_paths[:20],
            "changedPathsDuringScan": changed_paths,
            "changedPathSetSha256": digest,
        },
        {"lean/Sample.lean"}, {"lean/Sample.lean"},
        selected_scope=True, allow_unrelated_changes=True,
    )

    assert evidence["changedPathsDuringScan"] == changed_paths
    assert evidence["changedPathCountDuringScan"] == 25


def test_scoped_snapshot_evidence_rejects_tampered_changed_path_digest():
    with pytest.raises(ValueError, match="changed-path-set digest mismatch"):
        _snapshot_scope_evidence(
            {
                "worktreeConsistentDuringScan": False,
                "changedPathCountDuringScan": 1,
                "changedPathSampleDuringScan": ["docs/active.md"],
                "changedPathsDuringScan": ["docs/active.md"],
                "changedPathSetSha256": "0" * 64,
            },
            {"lean/Sample.lean"}, {"lean/Sample.lean"},
            selected_scope=True, allow_unrelated_changes=True,
        )


def test_scoped_snapshot_evidence_never_allows_full_scope_on_changed_worktree():
    with pytest.raises(ValueError, match="selected Git-event paths"):
        _snapshot_scope_evidence(
            {"worktreeConsistentDuringScan": False,
             "changedPathCountDuringScan": 1,
             "changedPathSampleDuringScan": ["docs/active.md"]},
            {"lean/Sample.lean"}, {"lean/Sample.lean"},
            selected_scope=False, allow_unrelated_changes=True,
        )


def test_each_current_infotree_node_links_to_shared_git_path_fossils(tmp_path: Path):
    repo = tmp_path / "repo"
    source = repo / "lean/Sample.lean"
    source.parent.mkdir(parents=True)
    source.write_text("theorem sample : True := True.intro\n")
    for args in (
        ("init", "-q"),
        ("config", "user.email", "test@example.invalid"),
        ("config", "user.name", "Test"),
        ("add", "lean/Sample.lean"),
        ("commit", "-q", "-m", "initial source"),
    ):
        subprocess.run(["git", "-C", str(repo), *args], check=True,
                       capture_output=True, text=True)
    git_head = subprocess.run(
        ["git", "-C", str(repo), "rev-parse", "HEAD"], check=True,
        capture_output=True, text=True,
    ).stdout.strip()
    source_sha = hashlib.sha256(source.read_bytes()).hexdigest()
    context_fp = "context-fingerprint"
    exporter = repo / "lean/DAG/RawInfoTreeExport.lean"
    exporter.parent.mkdir(parents=True)
    exporter.write_text("-- fixture exporter\n")
    capture = tmp_path / "exports/per_file/sample"
    capture.mkdir(parents=True)
    metadata = {
        "schema": "info_geometry.raw_infotree_export.v1",
        "file": "lean/Sample.lean",
        "module": "Sample",
        "node_count": 2,
        "root_count": 1,
        "fully_lossless": False,
        "loss_audited": True,
        "leakage_count": 1,
        "sourceProvenance": {
            "sourcePath": "lean/Sample.lean",
            "sourceSha256": source_sha,
            "leanContextFingerprint": context_fp,
            "exporterSourceSha256": hashlib.sha256(exporter.read_bytes()).hexdigest(),
        },
    }
    (capture / "metadata.json").write_text(json.dumps(metadata))
    _write_jsonl(capture / "raw_infotree_roots.jsonl", [
        {"rootKey": "root-1", "file": "lean/Sample.lean", "module": "Sample"},
    ])
    _write_jsonl(capture / "raw_infotree_projection_leakage.jsonl", [{
        "rootKey": "root-1", "nodeKey": "node-2", "field": "term_expr_graph",
        "reason": "not serialized",
    }])
    _write_jsonl(capture / "raw_infotree_nodes.jsonl", [
        {"nodeKey": "node-1", "rootKey": "root-1", "kind": "command", "depth": 0},
        {"nodeKey": "node-2", "rootKey": "root-1", "kind": "tactic", "depth": 1,
         "startPos": 0, "endPos": source.stat().st_size},
    ])
    _write_jsonl(capture / "raw_infotree_decl_links.jsonl", [
        {"linkKey": "decl-link-1", "nodeKey": "node-2", "rootKey": "root-1", "declKey": "decl-1",
         "declName": "Sample.sample", "module": "Sample"},
    ])
    with patch("tools.repository_evolution.infotree_dna._current_lean_context",
               return_value={"sourceSha256": source_sha, "fingerprint": context_fp}):
        dna = extract_one(capture, repo_root=repo)

    commit = git_head
    event = {
        "schema": "info_geometry.git_path_fossil_event.v1",
        "historyRevision": git_head,
        "artifactPath": "lean/Sample.lean",
        "commitSha": commit,
        "committerTimestamp": 100,
        "changeType": "A",
        "changedPath": "lean/Sample.lean",
    }
    event_path = tmp_path / "git-path-events.jsonl"
    event_bytes = (json.dumps(event, sort_keys=True) + "\n").encode()
    event_path.write_bytes(event_bytes)
    event_sha = hashlib.sha256(event_bytes).hexdigest()
    map_report = {
        "schema": "info_geometry.refactoring_map.v1",
        "sourceSnapshot": {
            "gitHead": git_head,
            "pathContentManifestSha256": "a" * 64,
            "filesystemTopologySha256": "d" * 64,
            "worktreeConsistentDuringScan": True,
        },
        "analysisProvenance": {
            "scannerSourceSha256": "b" * 64,
            "lakeManifestSha256": "c" * 64,
            "analysisInputsConsistentDuringScan": True,
        },
        "gitPathHistory": {
            "status": "path_history_candidate",
            "revision": git_head,
            "eventStreamCount": 1,
            "eventStreamSha256": event_sha,
            "eventStreamScope": {"mode": "selected_current_paths",
                                 "artifactPaths": ["lean/Sample.lean"]},
        },
        "files": [{
            "path": "lean/Sample.lean",
            "contentSha256": source_sha,
            "gitPathHistory": {
                "status": "path_continuity_candidate_not_content_identity",
                "touchCount": 1,
                "changeTypes": {"A": 1},
            },
        }],
    }
    output = tmp_path / "fossil-overlay"
    with patch("tools.repository_evolution.git_fossil_overlay._current_lean_context",
               return_value={"sourceSha256": source_sha, "fingerprint": context_fp}):
        manifest = build_git_fossil_overlay(
            map_report, {dna["artifactId"]: dna},
            {"lean/Sample.lean": (capture, metadata)}, event_path, output, repo,
        )

    links = [json.loads(line) for line in (output / "node_fossil_links.jsonl").read_text().splitlines()]
    assert manifest["nodeLinkCount"] == 2
    assert manifest["nodeLinksSha256"] == hashlib.sha256(
        (output / "node_fossil_links.jsonl").read_bytes()
    ).hexdigest()
    assert {row["nodeKey"] for row in links} == {"node-1", "node-2"}
    assert all(row["relation"] == "module_path_cohabitation" for row in links)
    assert all(row["pathFossilId"] == links[0]["pathFossilId"] for row in links)
    assert manifest["scannerSourceSha256"] == "b" * 64
    assert manifest["lakeManifestSha256"] == "c" * 64
    assert manifest["sourceSnapshotConsistency"] == {
        "status": "whole_worktree_consistent",
        "worktreeConsistentDuringScan": True,
        "selectedSourcePaths": ["lean/Sample.lean"],
    }
    assert all(row["generationId"] == manifest["generationId"] for row in links)
    decl_node = next(row for row in links if row["nodeKey"] == "node-2")
    assert decl_node["currentDeclarationLinks"][0]["declName"] == "Sample.sample"
    assert decl_node["captureLoss"]["leakageRowCount"] == 1
    decl_links = [json.loads(line) for line in
                  (output / "declaration_line_fossil_links.jsonl").read_text().splitlines()]
    assert manifest["declarationLineFossilLinkCount"] == 1
    assert manifest["sourceLineFossilSpanCount"] == 1
    assert decl_links[0]["linkKey"] == "decl-link-1"
    assert decl_links[0]["declKey"] == "decl-1"
    assert decl_links[0]["lineFossilStatus"] == "linked"
    assert len(decl_links[0]["lineFossilSpanIds"]) == 1


def test_fossil_overlay_rejects_event_stream_hash_mismatch(tmp_path: Path):
    report = {
        "schema": "info_geometry.refactoring_map.v1",
        "sourceSnapshot": {"gitHead": "2" * 40, "pathContentManifestSha256": "a" * 64,
                           "filesystemTopologySha256": "d" * 64,
                           "worktreeConsistentDuringScan": True},
        "analysisProvenance": {
            "scannerSourceSha256": "b" * 64,
            "lakeManifestSha256": "c" * 64,
            "analysisInputsConsistentDuringScan": True,
        },
        "gitPathHistory": {"status": "path_history_candidate", "revision": "2" * 40,
                           "eventStreamCount": 0, "eventStreamSha256": "0" * 64,
                           "eventStreamScope": {"mode": "all_current_paths"}},
        "files": [],
    }
    events = tmp_path / "empty.jsonl"
    events.write_text("")
    with pytest.raises(ValueError, match="hash does not match"):
        build_git_fossil_overlay(report, {}, {}, events, tmp_path / "out", tmp_path)


def test_overlay_generation_binds_scanner_and_manifest_provenance(tmp_path: Path):
    from tools.repository_evolution.git_fossil_overlay import _generation_id

    snapshot = {"gitHead": "2" * 40, "pathContentManifestSha256": "a" * 64,
                "filesystemTopologySha256": "d" * 64}
    provenance = {"scannerSourceSha256": "b" * 64,
                  "lakeManifestSha256": "c" * 64,
                  "analysisInputsConsistentDuringScan": True}
    generation = _generation_id(snapshot, provenance)
    changed_scanner = {**provenance, "scannerSourceSha256": "d" * 64}
    changed_manifest = {**provenance, "lakeManifestSha256": "e" * 64}
    changed_topology = {**snapshot, "filesystemTopologySha256": "f" * 64}
    assert _generation_id(snapshot, changed_scanner) != generation
    assert _generation_id(snapshot, changed_manifest) != generation
    assert _generation_id(changed_topology, provenance) != generation
    with pytest.raises(ValueError, match="changed or were unreadable"):
        _generation_id(snapshot, {**provenance, "analysisInputsConsistentDuringScan": False})
