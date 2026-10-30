#!/usr/bin/env python3
"""Link current InfoTree nodes to shared Git path-fossil streams.

This creates one pointer per current node and one path-event stream per current
source path. It never checks out or copies historical source revisions and
never claims that a path event proves historical declaration identity.
"""
from __future__ import annotations

import argparse
import bisect
import hashlib
import json
import os
import re
import subprocess
import sys
import tempfile
from collections import Counter
from pathlib import Path
from typing import Any, Iterator

_REPOSITORY_ROOT = Path(__file__).resolve().parents[2]
if str(_REPOSITORY_ROOT) not in sys.path:
    sys.path.insert(0, str(_REPOSITORY_ROOT))

from tools.repository_evolution.infotree_dna import (
    _current_lean_context,
    _sha256_file,
    capture_bundle_fingerprint,
    capture_file_digests,
)


MAP_SCHEMA = "info_geometry.refactoring_map.v1"
DNA_SCHEMA = "info_geometry.infotree_structural_dna.v1"
EVENT_SCHEMA = "info_geometry.git_path_fossil_event.v1"
LINE_FOSSIL_SCHEMA = "info_geometry.git_line_fossil_span.v1"
WORKTREE_LINE_SHA = "0" * 40


def _read_report(path: Path) -> dict[str, Any]:
    import gzip

    opener = gzip.open if path.suffix == ".gz" else open
    with opener(path, "rt", encoding="utf-8") as stream:
        report = json.load(stream)
    if not isinstance(report, dict):
        raise ValueError(f"{path}: expected JSON object")
    return report


def _jsonl(path: Path) -> Iterator[dict[str, Any]]:
    with path.open("r", encoding="utf-8") as stream:
        for line_number, line in enumerate(stream, 1):
            if not line.strip():
                continue
            try:
                row = json.loads(line)
            except json.JSONDecodeError as exc:
                raise ValueError(f"{path}:{line_number}: invalid JSON") from exc
            if not isinstance(row, dict):
                raise ValueError(f"{path}:{line_number}: expected JSON object")
            yield row


def _source_relative(repo_root: Path, source_path: Any) -> str:
    source = Path(str(source_path or ""))
    if not source.is_absolute():
        source = repo_root / source
    try:
        # The scanner keys Lake modules by lexical source path. Resolving an
        # in-tree symlink here would attach the module to its target's fossils.
        root = Path(os.path.abspath(os.fspath(repo_root)))
        lexical_source = Path(os.path.abspath(os.fspath(source)))
        return lexical_source.relative_to(root).as_posix()
    except ValueError as exc:
        raise ValueError(f"source path is outside repository: {source}") from exc


def _load_dna(path: Path) -> dict[str, dict[str, Any]]:
    records = {}
    for row in _jsonl(path):
        source = row.get("artifactId")
        if not isinstance(source, str) or row.get("schema") != DNA_SCHEMA:
            raise ValueError(f"{path}: malformed or unsupported InfoTree DNA record")
        if source in records:
            raise ValueError(f"duplicate InfoTree DNA record for {source}")
        records[source] = row
    return records


def _capture_index(exports_root: Path, repo_root: Path) -> dict[str, tuple[Path, dict[str, Any]]]:
    result = {}
    for metadata_path in sorted(exports_root.rglob("metadata.json")):
        if "merged" in metadata_path.relative_to(exports_root).parts:
            continue
        try:
            metadata = json.loads(metadata_path.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError) as exc:
            raise ValueError(f"{metadata_path}: unreadable capture metadata") from exc
        if metadata.get("schema") != "info_geometry.raw_infotree_export.v1":
            continue
        provenance = metadata.get("sourceProvenance")
        if not isinstance(provenance, dict):
            continue
        source = _source_relative(repo_root, provenance.get("sourcePath"))
        if _source_relative(repo_root, metadata.get("file")) != source:
            raise ValueError(f"{metadata_path}: metadata file differs from source provenance")
        if source in result:
            raise ValueError(f"duplicate RawInfoTree capture for current source {source}")
        result[source] = (metadata_path.parent, metadata)
    return result


def _validate_fossil_events(path: Path, report: dict[str, Any],
                            event_path_counts: Counter[str],
                            allowed_paths: set[str]) -> str:
    snapshot = report["sourceSnapshot"]
    git_head = snapshot.get("gitHead")
    digest = hashlib.sha256()
    count = 0
    with path.open("rb") as stream:
        for line_number, raw_line in enumerate(stream, 1):
            digest.update(raw_line)
            if not raw_line.strip():
                continue
            try:
                event = json.loads(raw_line)
            except json.JSONDecodeError as exc:
                raise ValueError(f"{path}:{line_number}: invalid JSON") from exc
            if event.get("schema") != EVENT_SCHEMA or event.get("historyRevision") != git_head:
                raise ValueError(f"{path}:{line_number}: event schema/revision differs from map")
            artifact_path = event.get("artifactPath")
            commit_sha = event.get("commitSha")
            if not isinstance(artifact_path, str) or not isinstance(commit_sha, str):
                raise ValueError(f"{path}:{line_number}: event lacks artifact/commit identity")
            if artifact_path not in allowed_paths:
                raise ValueError(f"{path}:{line_number}: event is outside declared path scope")
            event_path_counts[artifact_path] += 1
            count += 1
    declared_count = (report.get("gitPathHistory") or {}).get("eventStreamCount")
    if declared_count is not None and count != declared_count:
        raise ValueError("Git path event count does not match the refactoring map")
    actual_sha = digest.hexdigest()
    declared_sha = (report.get("gitPathHistory") or {}).get("eventStreamSha256")
    if declared_sha is not None and actual_sha != declared_sha:
        raise ValueError("Git path event stream hash does not match the refactoring map")
    return actual_sha


def _generation_id(snapshot: dict[str, Any], provenance: dict[str, Any]) -> str:
    """Bind an overlay generation to source, analyzer, and dependency-lock inputs."""
    scanner_sha = provenance.get("scannerSourceSha256")
    manifest_sha = provenance.get("lakeManifestSha256")
    if provenance.get("analysisInputsConsistentDuringScan") is not True:
        raise ValueError("refusing scanner/Lake inputs that changed or were unreadable during scan")
    if not isinstance(scanner_sha, str) or len(scanner_sha) != 64:
        raise ValueError("map lacks scanner source SHA-256 provenance")
    if not isinstance(manifest_sha, str) or len(manifest_sha) != 64:
        raise ValueError("map lacks Lake manifest SHA-256 provenance")
    source_sha = snapshot.get("pathContentManifestSha256")
    topology_sha = snapshot.get("filesystemTopologySha256")
    git_head = snapshot.get("gitHead")
    if not isinstance(source_sha, str) or not isinstance(git_head, str):
        raise ValueError("map lacks source-content or Git revision provenance")
    if not isinstance(topology_sha, str) or len(topology_sha) != 64:
        raise ValueError("map lacks filesystem-topology SHA-256 provenance")
    identity = {
        "gitHead": git_head,
        "pathContentManifestSha256": source_sha,
        "filesystemTopologySha256": topology_sha,
        "scannerSourceSha256": scanner_sha,
        "lakeManifestSha256": manifest_sha,
    }
    return hashlib.sha256(json.dumps(identity, sort_keys=True, separators=(",", ":"))
                          .encode("utf-8")).hexdigest()


def _snapshot_scope_evidence(snapshot: dict[str, Any], event_scope_paths: set[str],
                             dna_sources: set[str], selected_scope: bool,
                             allow_unrelated_changes: bool) -> dict[str, Any]:
    """Describe the consistency actually established for this overlay scope.

    A whole-worktree scan remains the default requirement. An explicitly
    selected-source overlay may proceed over a globally changing worktree only
    when the scanner reports its complete changed-path set and none of those
    paths intersects the selected Git-event or DNA-source scope. This records
    scope-level evidence; it does not relabel the whole map as consistent.
    """
    if snapshot.get("worktreeConsistentDuringScan") is True:
        return {
            "status": "whole_worktree_consistent",
            "worktreeConsistentDuringScan": True,
            "selectedSourcePaths": sorted(dna_sources),
        }
    if not allow_unrelated_changes:
        raise ValueError("refusing inconsistent source/git snapshot")
    if not selected_scope:
        raise ValueError("scoped inconsistency allowance requires selected Git-event paths")

    changed_count = snapshot.get("changedPathCountDuringScan")
    changed_paths = snapshot.get("changedPathsDuringScan")
    if changed_paths is None:
        # Old maps are accepted only if their sample is demonstrably complete.
        changed_paths = snapshot.get("changedPathSampleDuringScan")
    if (isinstance(changed_count, bool) or not isinstance(changed_count, int)
            or changed_count < 0 or not isinstance(changed_paths, list)
            or any(not isinstance(path, str) or not path for path in changed_paths)
            or len(changed_paths) != changed_count
            or len(set(changed_paths)) != changed_count
            or changed_paths != sorted(changed_paths)):
        raise ValueError("cannot verify overlay scope: scanner did not report every changed path")
    declared_digest = snapshot.get("changedPathSetSha256")
    if declared_digest is not None:
        observed_digest = hashlib.sha256(json.dumps(
            changed_paths, ensure_ascii=False, separators=(",", ":")
        ).encode("utf-8")).hexdigest()
        if declared_digest != observed_digest:
            raise ValueError("cannot verify overlay scope: changed-path-set digest mismatch")
    changed_path_set = set(changed_paths)
    if changed_path_set & event_scope_paths:
        raise ValueError("selected Git-event scope intersects paths changed during scan")
    if changed_path_set & dna_sources:
        raise ValueError("selected InfoTree DNA source changed during scan")
    return {
        "status": "selected_scope_disjoint_from_observed_worktree_changes",
        "worktreeConsistentDuringScan": False,
        "changedPathCountDuringScan": changed_count,
        "changedPathsDuringScan": changed_paths,
        "selectedSourcePaths": sorted(dna_sources),
        "selectedGitEventPaths": sorted(event_scope_paths),
    }


def _parse_blame_porcelain(text: str) -> list[dict[str, Any]]:
    """Read one --line-porcelain attribution row per current source line."""
    lines = text.splitlines()
    records: list[dict[str, Any]] = []
    index = 0
    header_re = re.compile(r"^(\^?[0-9a-f]{40}) (\d+) (\d+)(?: (\d+))?$")
    while index < len(lines):
        match = header_re.match(lines[index])
        if match is None:
            raise ValueError(f"malformed git blame header at output line {index + 1}")
        commit_sha = match.group(1).lstrip("^")
        origin_line = int(match.group(2))
        final_line = int(match.group(3))
        index += 1
        fields: dict[str, str] = {}
        while index < len(lines) and not lines[index].startswith("\t"):
            field_line = lines[index]
            key, separator, value = field_line.partition(" ")
            if separator:
                fields[key] = value
            else:
                fields[key] = ""
            index += 1
        if index >= len(lines):
            raise ValueError(f"git blame line {final_line} lacks source text")
        index += 1  # porcelain source text
        author_time = fields.get("author-time")
        records.append({
            "commitSha": commit_sha,
            "originLine": origin_line,
            "finalLine": final_line,
            "originPath": fields.get("filename"),
            "authorTime": int(author_time) if author_time and author_time.isdigit() else None,
        })
    return records


def _current_line_fossils(repo_root: Path, source: str, git_head: str,
                          expected_source_sha: str) -> tuple[list[dict[str, Any]], str]:
    """Attribute current file lines to commits without checking out old trees.

    ``git blame --contents`` compares the current working-tree bytes to the
    specified immutable revision. Lines absent from that revision carry Git's
    all-zero pseudo-commit and are retained as uncommitted evidence.
    """
    source_path = repo_root / source
    if source_path.is_symlink():
        return [], "skipped_lexical_symlink_target_bytes"
    if not source_path.is_file():
        return [], "source_file_missing"
    try:
        completed = subprocess.run(
            ["git", "-C", str(repo_root), "blame", "--line-porcelain",
             "--contents", str(source_path), git_head, "--", source],
            check=False, capture_output=True, text=True, encoding="utf-8", errors="replace",
        )
    except OSError:
        return [], "git_blame_process_unavailable"
    if completed.returncode != 0:
        return [], "git_blame_unavailable_for_path"
    try:
        records = _parse_blame_porcelain(completed.stdout)
    except (ValueError, UnicodeError):
        return [], "git_blame_output_malformed"
    if _sha256_file(source_path) != expected_source_sha:
        raise ValueError(f"current source changed while collecting Git line fossils: {source}")
    current_bytes = source_path.read_bytes()
    expected_lines = current_bytes.count(b"\n") + (
        1 if current_bytes and not current_bytes.endswith(b"\n") else 0
    )
    if len(records) != expected_lines or any(
            row["finalLine"] != line for line, row in enumerate(records, 1)):
        return [], "git_blame_line_coverage_mismatch"

    spans: list[dict[str, Any]] = []
    for record in records:
        if spans:
            previous = spans[-1]
            same_origin = (
                previous["commitSha"] == record["commitSha"]
                and previous["originPath"] == record["originPath"]
                and previous["authorTime"] == record["authorTime"]
                and previous["originEndLine"] == record["originLine"]
                and previous["endLineExclusive"] == record["finalLine"]
            )
            if same_origin:
                previous["endLineExclusive"] += 1
                previous["originEndLine"] += 1
                previous["lineCount"] += 1
                continue
        spans.append({
            "commitSha": record["commitSha"],
            "originPath": record["originPath"],
            "originStartLine": record["originLine"],
            "originEndLine": record["originLine"] + 1,
            "startLine": record["finalLine"],
            "endLineExclusive": record["finalLine"] + 1,
            "lineCount": 1,
            "authorTime": record["authorTime"],
            "originStatus": ("uncommitted_current_content"
                             if record["commitSha"] == WORKTREE_LINE_SHA
                             else "committed_line_origin"),
        })
    return spans, "complete"


def _node_source_span(node: dict[str, Any], source_bytes: bytes,
                      line_starts: list[int] | None = None) -> dict[str, Any] | None:
    start = node.get("startPos")
    end = node.get("endPos")
    if (isinstance(start, bool) or not isinstance(start, int)
            or isinstance(end, bool) or not isinstance(end, int)):
        return None
    if start < 0 or end < start or end > len(source_bytes):
        return None
    if line_starts is None:
        line_starts = [0]
        line_starts.extend(index + 1 for index, byte in enumerate(source_bytes) if byte == 10)
    start_line = bisect.bisect_right(line_starts, start)
    end_line_exclusive = (start_line if end == start
                          else bisect.bisect_left(line_starts, end) + 1)
    return {
        "startByte": start,
        "endByte": end,
        "startLine": start_line,
        "endLineExclusive": max(start_line, end_line_exclusive),
    }


def build_git_fossil_overlay(refactoring_map: dict[str, Any], dna_records: dict[str, dict[str, Any]],
                             captures: dict[str, tuple[Path, dict[str, Any]]],
                             git_path_events: Path, output_dir: Path,
                             repo_root: Path,
                             allow_unrelated_worktree_changes: bool = False) -> dict[str, Any]:
    """Validate generation bindings and write current-node to path-fossil links."""
    if refactoring_map.get("schema") != MAP_SCHEMA:
        raise ValueError(f"expected {MAP_SCHEMA}")
    snapshot = refactoring_map.get("sourceSnapshot") or {}
    provenance = refactoring_map.get("analysisProvenance") or {}
    generation_id = _generation_id(snapshot, provenance)
    git_head = snapshot.get("gitHead")
    history = refactoring_map.get("gitPathHistory") or {}
    if history.get("status") != "path_history_candidate" or history.get("revision") != git_head:
        raise ValueError("map lacks path fossils bound to its exact Git HEAD")
    if not isinstance(history.get("eventStreamCount"), int) or not isinstance(
            history.get("eventStreamSha256"), str):
        raise ValueError("map must bind the full Git path-event stream by count and SHA-256")
    if output_dir.exists():
        raise FileExistsError(f"refusing to overwrite fossil overlay directory: {output_dir}")
    file_records = {row["path"]: row for row in refactoring_map.get("files", [])
                    if isinstance(row, dict) and isinstance(row.get("path"), str)}
    scope = history.get("eventStreamScope")
    if not isinstance(scope, dict):
        raise ValueError("map must declare the Git path-event coverage scope")
    if scope.get("mode") == "all_current_paths":
        event_scope_paths = set(file_records)
    elif scope.get("mode") == "selected_current_paths":
        paths = scope.get("artifactPaths")
        if not isinstance(paths, list) or any(not isinstance(path, str) for path in paths):
            raise ValueError("selected Git path-event scope requires artifactPaths")
        event_scope_paths = set(paths)
        if len(event_scope_paths) != len(paths) or not event_scope_paths <= set(file_records):
            raise ValueError("Git path-event scope contains duplicate or unknown artifact paths")
    else:
        raise ValueError("unsupported Git path-event scope")
    if not set(dna_records) <= event_scope_paths:
        raise ValueError("path-event stream does not cover every InfoTree DNA source")
    snapshot_scope_evidence = _snapshot_scope_evidence(
        snapshot,
        event_scope_paths,
        set(dna_records),
        scope.get("mode") == "selected_current_paths",
        allow_unrelated_worktree_changes,
    )
    event_counts: Counter[str] = Counter()
    event_stream_sha = _validate_fossil_events(
        git_path_events, refactoring_map, event_counts, event_scope_paths
    )
    unknown_event_paths = set(event_counts) - set(file_records)
    if unknown_event_paths:
        raise ValueError(f"Git path events refer to paths absent from scanner map: {sorted(unknown_event_paths)[:5]}")
    for source in event_scope_paths:
        record = file_records[source]
        path_history = record.get("gitPathHistory")
        if isinstance(path_history, dict):
            expected = int(path_history.get("touchCount", 0))
            if event_counts[source] != expected:
                raise ValueError(f"path-event coverage differs from map summary for {source}")

    map_manifest = snapshot.get("pathContentManifestSha256")
    for source, dna in dna_records.items():
        record = file_records.get(source)
        if record is None:
            raise ValueError(f"InfoTree DNA source is missing from scanner map: {source}")
        if dna.get("sourceSha256") != record.get("contentSha256"):
            raise ValueError(f"InfoTree DNA source digest differs from scanner map: {source}")
        source_path = repo_root / source
        if not source_path.is_file() or _sha256_file(source_path) != dna.get("sourceSha256"):
            raise ValueError(f"current source changed after scanner/DNA capture: {source}")
        current_context = _current_lean_context(repo_root, source_path)
        if (current_context.get("sourceSha256") != dna.get("sourceSha256")
                or current_context.get("fingerprint") != dna.get("leanContextFingerprint")):
            raise ValueError(f"Lean source/toolchain/olean context changed for {source}")
        if dna.get("schema") != DNA_SCHEMA:
            raise ValueError(f"unsupported InfoTree DNA record for {source}")
        capture = captures.get(source)
        if capture is None:
            raise ValueError(f"no source-provenance RawInfoTree capture for {source}")
        export_dir, metadata = capture
        capture_source_provenance = metadata.get("sourceProvenance") or {}
        producer_sha = dna.get("exporterSourceSha256")
        producer_path = repo_root / "lean/DAG/RawInfoTreeExport.lean"
        if (not isinstance(producer_sha, str) or len(producer_sha) != 64
                or capture_source_provenance.get("exporterSourceSha256") != producer_sha
                or not producer_path.is_file() or _sha256_file(producer_path) != producer_sha):
            raise ValueError(f"capture/DNA exporter source receipt is missing or stale for {source}")
        if (capture_source_provenance.get("sourceSha256") != dna.get("sourceSha256")
                or capture_source_provenance.get("leanContextFingerprint") != dna.get("leanContextFingerprint")):
            raise ValueError(f"capture and compact DNA provenance differ for {source}")
        file_digests = capture_file_digests(export_dir)
        if file_digests != dna.get("rawRowFileSha256"):
            raise ValueError(f"raw capture row files changed after DNA extraction for {source}")
        if capture_bundle_fingerprint(file_digests) != dna.get("rawCaptureSha256"):
            raise ValueError(f"raw capture bundle fingerprint mismatch for {source}")

    output_dir.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(prefix=f".{output_dir.name}.stage-", dir=output_dir.parent) as temp:
        staging = Path(temp)
        links_path = staging / "node_fossil_links.jsonl"
        declaration_links_path = staging / "declaration_line_fossil_links.jsonl"
        line_fossils_path = staging / "source_line_fossils.jsonl"
        links_digest = hashlib.sha256()
        declaration_links_digest = hashlib.sha256()
        line_fossils_digest = hashlib.sha256()
        link_count = 0
        declaration_link_count = 0
        declaration_line_edge_count = 0
        line_fossil_count = 0
        line_fossil_statuses: Counter[str] = Counter()
        node_count_by_source: Counter[str] = Counter()
        source_lineage_features: dict[str, dict[str, Any]] = {}
        source_line_index: dict[str, tuple[bytes, list[int], list[dict[str, Any]], list[str], str]] = {}
        with line_fossils_path.open("w", encoding="utf-8") as line_out:
            for source, dna in sorted(dna_records.items()):
                source_bytes = (repo_root / source).read_bytes()
                source_sha = hashlib.sha256(source_bytes).hexdigest()
                if source_sha != dna["sourceSha256"]:
                    raise ValueError(f"current source changed before Git line blame: {source}")
                segments, blame_status = _current_line_fossils(
                    repo_root, source, git_head, source_sha
                )
                line_count = source_bytes.count(b"\n") + (
                    1 if source_bytes and not source_bytes.endswith(b"\n") else 0
                )
                committed_segments = [
                    segment for segment in segments
                    if segment["originStatus"] == "committed_line_origin"
                ]
                current_content_segments = [
                    segment for segment in segments
                    if segment["originStatus"] == "uncommitted_current_content"
                ]
                source_lineage_features[source] = {
                    "schema": "info_geometry.source_lineage_features.v1",
                    "generationId": generation_id,
                    "historyRevision": git_head,
                    "sourcePath": source,
                    "sourceSha256": source_sha,
                    "lineAttributionStatus": blame_status,
                    "lineCount": line_count,
                    "attributedLineCount": sum(int(row["lineCount"]) for row in segments),
                    "committedLineCount": sum(int(row["lineCount"]) for row in committed_segments),
                    "currentContentLineCount": sum(
                        int(row["lineCount"]) for row in current_content_segments
                    ),
                    "distinctCommitCount": len({row["commitSha"] for row in committed_segments}),
                    "distinctOriginPathCount": len({
                        row["originPath"] for row in committed_segments if row["originPath"]
                    }),
                    "declarationLinkCount": 0,
                    "declarationWithLineOriginCount": 0,
                    "distinctDeclarationCount": 0,
                    "_declarationKeys": set(),
                }
                line_starts = [0]
                line_starts.extend(index + 1 for index, byte in enumerate(source_bytes) if byte == 10)
                line_fossil_statuses[blame_status] += 1
                ids: list[str] = []
                for segment_index, segment in enumerate(segments):
                    span_id = hashlib.sha256(
                        f"{generation_id}\0{source}\0{segment_index}".encode(
                            "utf-8", errors="surrogateescape"
                        )
                    ).hexdigest()
                    row = {
                        "schema": LINE_FOSSIL_SCHEMA,
                        "generationId": generation_id,
                        "historyRevision": git_head,
                        "lineFossilSpanId": span_id,
                        "sourcePath": source,
                        "sourceSha256": source_sha,
                        **segment,
                    }
                    serialized = json.dumps(row, sort_keys=True, ensure_ascii=False) + "\n"
                    line_out.write(serialized)
                    line_fossils_digest.update(serialized.encode("utf-8"))
                    line_fossil_count += 1
                    ids.append(span_id)
                # Kept in-memory only for this source while its nodes stream.
                source_line_index[source] = (source_bytes, line_starts, segments, ids, blame_status)
        with links_path.open("w", encoding="utf-8") as out, \
                declaration_links_path.open("w", encoding="utf-8") as declaration_out:
            for source, dna in sorted(dna_records.items()):
                export_dir, metadata = captures[source]
                (source_bytes, line_starts, line_segments,
                 line_segment_ids, blame_status) = source_line_index[source]
                roots: dict[str, str] = {}
                for root in _jsonl(export_dir / "raw_infotree_roots.jsonl"):
                    file_path = root.get("file")
                    if file_path != source:
                        raise ValueError(f"root file does not match captured source {source}")
                    roots[str(root.get("rootKey"))] = source
                declaration_links: dict[str, list[dict[str, Any]]] = {}
                decl_path = export_dir / "raw_infotree_decl_links.jsonl"
                if decl_path.is_file():
                    for link in _jsonl(decl_path):
                        declaration_links.setdefault(str(link.get("nodeKey")), []).append({
                            "linkKey": link.get("linkKey"),
                            "declKey": link.get("declKey"),
                            "declName": link.get("declName"),
                            "module": link.get("module"),
                        })
                path_history = file_records[source].get("gitPathHistory") or {}
                path_fossil_id = hashlib.sha256(
                    f"{git_head}\0{source}".encode("utf-8", errors="surrogateescape")
                ).hexdigest()
                nodes_path = export_dir / "raw_infotree_nodes.jsonl"
                actual_nodes = 0
                for node in _jsonl(nodes_path):
                    root_key = str(node.get("rootKey", ""))
                    if root_key not in roots:
                        raise ValueError(f"node references unknown root in {source}: {root_key}")
                    actual_nodes += 1
                    source_span = _node_source_span(node, source_bytes, line_starts)
                    intersecting_fossil_ids: list[str] = []
                    if source_span is not None and blame_status == "complete":
                        intersecting_fossil_ids = [
                            line_segment_ids[index]
                            for index, segment in enumerate(line_segments)
                            if segment["startLine"] < source_span["endLineExclusive"]
                            and source_span["startLine"] < segment["endLineExclusive"]
                        ]
                    row = {
                        "schema": "info_geometry.infotree_node_git_fossil_link.v1",
                        "generationId": generation_id,
                        "currentSourcePath": source,
                        "sourceSha256": dna["sourceSha256"],
                        "leanContextFingerprint": dna["leanContextFingerprint"],
                        "rawCaptureSha256": dna["rawCaptureSha256"],
                        "rootKey": root_key,
                        "nodeKey": node.get("nodeKey"),
                        "nodeKind": node.get("kind"),
                        "depth": node.get("depth"),
                        "pathFossilId": path_fossil_id,
                        "sourceSpan": source_span,
                        "lineFossilSpanIds": intersecting_fossil_ids,
                        "lineFossilStatus": ("linked" if intersecting_fossil_ids
                                             else "no_source_span" if source_span is None
                                             else blame_status),
                        "historyRevision": git_head,
                        "fossilEventCount": event_counts[source],
                        "pathHistoryStatus": path_history.get("status"),
                        "relation": "module_path_cohabitation",
                        "currentDeclarationLinks": declaration_links.get(str(node.get("nodeKey")), []),
                        "captureLoss": {
                            "fullyLossless": metadata.get("fully_lossless") is True,
                            "leakageRowCount": int(metadata.get("leakage_count", 0) or 0),
                        },
                        "authority": "current InfoTree node plus Git path fossils; no historical declaration identity claim",
                    }
                    serialized_link = json.dumps(row, sort_keys=True, ensure_ascii=False) + "\n"
                    out.write(serialized_link)
                    links_digest.update(serialized_link.encode("utf-8"))
                    link_count += 1
                    for decl_link in declaration_links.get(str(node.get("nodeKey")), []):
                        declaration_row = {
                            "schema": "info_geometry.declaration_line_fossil_link.v1",
                            "generationId": generation_id,
                            "historyRevision": git_head,
                            "currentSourcePath": source,
                            "sourceSha256": dna["sourceSha256"],
                            "leanContextFingerprint": dna["leanContextFingerprint"],
                            "rootKey": root_key,
                            "nodeKey": node.get("nodeKey"),
                            "sourceSpan": source_span,
                            "lineFossilSpanIds": intersecting_fossil_ids,
                            "lineFossilStatus": ("linked" if intersecting_fossil_ids
                                                 else "no_source_span" if source_span is None
                                                 else blame_status),
                            **decl_link,
                            "relation": "current_declaration_line_origin_overlap",
                            "authority": "current RawInfoTree declaration link and source span; no historical declaration identity claim",
                        }
                        serialized_declaration = (
                            json.dumps(declaration_row, sort_keys=True, ensure_ascii=False) + "\n"
                        )
                        declaration_out.write(serialized_declaration)
                        declaration_links_digest.update(serialized_declaration.encode("utf-8"))
                        declaration_link_count += 1
                        declaration_line_edge_count += len(intersecting_fossil_ids)
                        source_features = source_lineage_features[source]
                        source_features["declarationLinkCount"] += 1
                        if intersecting_fossil_ids:
                            source_features["declarationWithLineOriginCount"] += 1
                        source_features["_declarationKeys"].add(decl_link.get("declKey"))
                expected_nodes = int(dna.get("rowCounts", {}).get("raw_infotree_nodes.jsonl", 0))
                metadata_nodes = int(metadata.get("node_count", -1))
                if actual_nodes != expected_nodes or actual_nodes != metadata_nodes:
                    raise ValueError(f"RawInfoTree node count mismatch for {source}")
                if hashlib.sha256((repo_root / source).read_bytes()).hexdigest() != dna["sourceSha256"]:
                    raise ValueError(f"current source changed while linking node spans: {source}")
                node_count_by_source[source] = actual_nodes
        for source_features in source_lineage_features.values():
            declaration_keys = source_features.pop("_declarationKeys")
            source_features["distinctDeclarationCount"] = len(declaration_keys)
        lineage_features_json = json.dumps(
            source_lineage_features, sort_keys=True, ensure_ascii=False, separators=(",", ":")
        )
        lineage_features_sha = hashlib.sha256(lineage_features_json.encode("utf-8")).hexdigest()
        manifest = {
            "schema": "info_geometry.git_fossil_overlay_manifest.v1",
            "generationId": generation_id,
            "gitHead": git_head,
            "sourceSnapshotConsistency": snapshot_scope_evidence,
            "pathContentManifestSha256": map_manifest,
            "filesystemTopologySha256": snapshot["filesystemTopologySha256"],
            "scannerSourceSha256": provenance["scannerSourceSha256"],
            "lakeManifestSha256": provenance["lakeManifestSha256"],
            "gitPathEventsSha256": event_stream_sha,
            "gitPathEventCount": sum(event_counts.values()),
            "nodeLinksSha256": links_digest.hexdigest(),
            "declarationLineFossilLinksSha256": declaration_links_digest.hexdigest(),
            "declarationLineFossilLinkCount": declaration_link_count,
            "declarationLineFossilEdgeCount": declaration_line_edge_count,
            "sourceLineFossilsSha256": line_fossils_digest.hexdigest(),
            "sourceLineFossilSpanCount": line_fossil_count,
            "sourceLineFossilStatusCounts": dict(sorted(line_fossil_statuses.items())),
            "sourceLineageFeaturesByPath": dict(sorted(source_lineage_features.items())),
            "sourceLineageFeaturesSha256": lineage_features_sha,
            "sourceCount": len(dna_records),
            "nodeLinkCount": link_count,
            "nodesBySource": dict(sorted(node_count_by_source.items())),
            "relation": "module_path_cohabitation",
            "authority": "current source and compiler observations linked to compact Git path-event fossils",
        }
        (staging / "metadata.json").write_text(
            json.dumps(manifest, sort_keys=True, indent=2) + "\n", encoding="utf-8"
        )
        staging.rename(output_dir)
    return manifest


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("refactoring_map", type=Path)
    parser.add_argument("infotree_dna", type=Path, help="compact DNA JSONL from infotree_dna.py")
    parser.add_argument("infotree_exports", type=Path, help="batch capture per_file tree")
    parser.add_argument("git_path_events", type=Path, help="full JSONL fossil event stream")
    parser.add_argument("--repo-root", type=Path, default=Path(__file__).resolve().parents[2])
    parser.add_argument("--out-dir", type=Path, required=True)
    parser.add_argument(
        "--allow-unrelated-worktree-changes",
        action="store_true",
        help=("allow a selected-source overlay when every path changed during the map scan is "
              "reported and disjoint from its selected source/event scope"),
    )
    args = parser.parse_args()
    report = _read_report(args.refactoring_map)
    dna = _load_dna(args.infotree_dna)
    captures = _capture_index(args.infotree_exports, args.repo_root)
    result = build_git_fossil_overlay(report, dna, captures, args.git_path_events,
                                      args.out_dir, args.repo_root,
                                      allow_unrelated_worktree_changes=args.allow_unrelated_worktree_changes)
    print(json.dumps(result, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
