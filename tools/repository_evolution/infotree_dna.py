#!/usr/bin/env python3
"""Stream current, source-bound InfoTree captures into compact DNA features.

This is an extractor for candidate taxonomy inputs, not a semantic classifier.
It reads one per-file export at a time, never copies source revisions, and
rejects exports whose recorded source digest no longer matches the worktree.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
import sys
from collections import Counter
from pathlib import Path
from typing import Any, Iterable


ROOT = Path(__file__).resolve().parents[2]
if __package__ in (None, ""):
    sys.path.insert(0, str(ROOT))

FEATURE_VERSION = "raw_infotree_structural_dna.v4"
ROW_FILES = {
    "raw_infotree_roots.jsonl": "root",
    "raw_infotree_nodes.jsonl": "node",
    "raw_infotree_edges.jsonl": "tree_edge",
    "raw_infotree_contexts.jsonl": "context",
    "raw_infotree_payloads.jsonl": "payload",
    "raw_infotree_payload_fields.jsonl": "payload_field",
    "raw_infotree_decl_links.jsonl": "decl_link",
    "raw_infotree_env_refs.jsonl": "env_ref",
    "raw_infotree_mctx_refs.jsonl": "mctx_ref",
    "raw_infotree_mctx_decls.jsonl": "mctx_decl",
    "raw_infotree_lctx_refs.jsonl": "lctx_ref",
    "raw_infotree_lctx_decls.jsonl": "lctx_decl",
    "raw_infotree_goal_states.jsonl": "goal_state",
    "raw_infotree_fvar_lineage.jsonl": "fvar_lineage",
    "raw_infotree_tactic_arguments.jsonl": "tactic_argument",
    "raw_infotree_messages.jsonl": "message",
    "raw_infotree_projection_leakage.jsonl": "projection_leakage",
}


def _sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def _bucket_nat(value: Any) -> str:
    try:
        number = max(0, int(value))
    except (TypeError, ValueError):
        return "unknown"
    if number == 0:
        return "0"
    if number == 1:
        return "1"
    if number <= 4:
        return "2-4"
    if number <= 16:
        return "5-16"
    return "17+"


def _inc(features: Counter[str], name: str, value: Any) -> None:
    if value is None or value == "":
        return
    features[f"{name}={str(value).strip().lower()}"] += 1


def _add_row_features(features: Counter[str], family: str, row: dict[str, Any]) -> None:
    if family == "root":
        # Root identity fields (module/path/key) are provenance, not model
        # features. Count roots while the raw bundle hash binds their contents.
        features["root.count"] += 1
    elif family == "node":
        _inc(features, "node.kind", row.get("kind"))
        features[f"node.depth_bucket={_bucket_nat(row.get('depth'))}"] += 1
        features[f"node.branching_bucket={_bucket_nat(row.get('branchingFactor'))}"] += 1
        _inc(features, "node.logical", row.get("isLogical"))
    elif family == "tree_edge":
        features[f"tree_edge.sibling_bucket={_bucket_nat(row.get('siblingIndex'))}"] += 1
    elif family == "context":
        _inc(features, "context.kind", row.get("contextKind"))
    elif family == "payload":
        _inc(features, "payload.kind", row.get("kind"))
    elif family == "payload_field":
        _inc(features, "payload_field.name", row.get("field"))
    elif family == "env_ref":
        _inc(features, "env_ref.role", row.get("role"))
        _inc(features, "env_ref.present", row.get("present"))
    elif family == "mctx_ref":
        _inc(features, "mctx_ref.role", row.get("role"))
    elif family == "lctx_ref":
        _inc(features, "lctx_ref.source_kind", row.get("sourceKind"))
    elif family == "goal_state":
        _inc(features, "goal_state.role", row.get("role"))
    elif family == "fvar_lineage":
        _inc(features, "fvar_lineage.role", row.get("role"))
    elif family == "tactic_argument":
        _inc(features, "tactic_argument.kind", row.get("kind"))
    elif family == "message":
        _inc(features, "message.severity", row.get("severity"))
    elif family == "projection_leakage":
        # Leakage is part of the structural observation: retain standardized
        # omitted-field identities, but exclude prose reasons from features.
        _inc(features, "projection_leakage.field", row.get("field"))
    # Identifiers, theorem names, path names, source text, hashes, and local
    # context values are intentionally omitted from the model feature vector.


def _iter_jsonl(path: Path, digest: Any | None = None) -> Iterable[dict[str, Any]]:
    with path.open("rb") as stream:
        for line_number, raw_line in enumerate(stream, start=1):
            if digest is not None:
                digest.update(raw_line)
            try:
                line = raw_line.decode("utf-8")
            except UnicodeDecodeError as exc:
                raise ValueError(f"{path}:{line_number}: invalid UTF-8") from exc
            if not line.strip():
                continue
            try:
                row = json.loads(line)
            except json.JSONDecodeError as exc:
                raise ValueError(f"{path}:{line_number}: invalid JSON") from exc
            if not isinstance(row, dict):
                raise ValueError(f"{path}:{line_number}: expected a JSON object")
            yield row


def capture_bundle_fingerprint(file_digests: dict[str, str]) -> str:
    """Fingerprint the exact named raw row files without copying their bytes."""
    payload = json.dumps({"schema": "info_geometry.raw_infotree_bundle.v1",
                          "files": dict(sorted(file_digests.items()))},
                         sort_keys=True, separators=(",", ":"))
    return hashlib.sha256(payload.encode("utf-8")).hexdigest()


def capture_file_digests(export_dir: Path) -> dict[str, str]:
    """Hash present row files in bounded memory for a later exact-capture join."""
    digests: dict[str, str] = {}
    for filename in ROW_FILES:
        path = export_dir / filename
        if path.is_file():
            digests[filename] = _sha256_file(path)
    return digests


def _current_lean_context(repo_root: Path, source_path: Path) -> dict[str, Any]:
    """Fingerprint Lean/.olean inputs under the same lock used by all Lake work."""
    from tools.build_lock import acquire_build_lock
    from tools.infra.pantograph_environment import build_lean_context_manifest

    lock = acquire_build_lock(
        None, f"infotree-dna-context:{os.getpid()}:{source_path}", block=True
    )
    try:
        return build_lean_context_manifest(repo_root, source_path)
    finally:
        lock.release()


def _lexical_repo_source_path(repo_root: Path, source_path: Path) -> tuple[Path, str]:
    """Keep the repository path identity while normalizing ``..`` components.

    Lake may compile a Lean module through an in-tree symlink. Resolving that
    symlink here would replace the module's source identity with its target's
    path and join the InfoTree capture to the wrong Git path history.
    """
    root = Path(os.path.abspath(os.fspath(repo_root)))
    source = source_path if source_path.is_absolute() else root / source_path
    source = Path(os.path.abspath(os.fspath(source)))
    try:
        relative = source.relative_to(root).as_posix()
    except ValueError as exc:
        raise ValueError("source path is outside this repository") from exc
    return source, relative


def extract_one(export_dir: Path, *, repo_root: Path = ROOT) -> dict[str, Any]:
    """Extract one per-file capture after checking source-generation binding."""
    metadata_path = export_dir / "metadata.json"
    metadata = json.loads(metadata_path.read_text(encoding="utf-8"))
    if metadata.get("schema") != "info_geometry.raw_infotree_export.v1":
        raise ValueError(f"{metadata_path}: expected a single-file RawInfoTree export")
    if metadata.get("loss_audited") is not True:
        raise ValueError(f"{metadata_path}: capture has not passed the loss audit")
    provenance = metadata.get("sourceProvenance")
    if not isinstance(provenance, dict):
        raise ValueError(f"{metadata_path}: no source provenance; batch-captured export required")
    source_path_value = Path(str(provenance.get("sourcePath") or ""))
    try:
        source_path, repo_relative_source = _lexical_repo_source_path(
            repo_root, source_path_value
        )
    except ValueError as exc:
        raise ValueError(f"{metadata_path}: {exc}") from exc
    expected_sha = str(provenance.get("sourceSha256") or "")
    if len(expected_sha) != 64 or _sha256_file(source_path) != expected_sha:
        raise ValueError(f"{metadata_path}: current source digest does not match capture")
    exporter_sha = provenance.get("exporterSourceSha256")
    exporter_path = repo_root / "lean/DAG/RawInfoTreeExport.lean"
    if (not isinstance(exporter_sha, str) or len(exporter_sha) != 64
            or not exporter_path.is_file() or _sha256_file(exporter_path) != exporter_sha):
        raise ValueError(f"{metadata_path}: exporter source receipt missing or stale")
    expected_context = str(provenance.get("leanContextFingerprint") or "")
    current_context = _current_lean_context(repo_root, source_path)
    if current_context.get("sourceSha256") != expected_sha:
        raise ValueError(f"{metadata_path}: source changed while context provenance was checked")
    if not expected_context or current_context.get("fingerprint") != expected_context:
        raise ValueError(f"{metadata_path}: Lean toolchain/olean context differs from capture")
    leakage_count = metadata.get("leakage_count")
    fully_lossless = metadata.get("fully_lossless")
    if (isinstance(leakage_count, bool) or not isinstance(leakage_count, int)
            or leakage_count < 0):
        raise ValueError(f"{metadata_path}: leakage_count must be a nonnegative integer")
    if not isinstance(fully_lossless, bool):
        raise ValueError(f"{metadata_path}: fully_lossless must be boolean")
    if fully_lossless and leakage_count:
        raise ValueError(f"{metadata_path}: lossless capture reports projection leakage")
    roots_path = export_dir / "raw_infotree_roots.jsonl"
    if not roots_path.is_file():
        raise ValueError(f"{metadata_path}: required RawInfoTree roots file is missing")
    leakage_path = export_dir / "raw_infotree_projection_leakage.jsonl"
    if not leakage_path.is_file():
        raise ValueError(f"{metadata_path}: required RawInfoTree projection leakage file is missing")

    features: Counter[str] = Counter()
    row_counts: Counter[str] = Counter()
    row_file_digests: dict[str, str] = {}
    for filename, family in ROW_FILES.items():
        path = export_dir / filename
        if not path.is_file():
            continue
        digest = hashlib.sha256()
        for row in _iter_jsonl(path, digest):
            row_counts[filename] += 1
            _add_row_features(features, family, row)
        row_file_digests[filename] = digest.hexdigest()

    feature_rows = dict(sorted(features.items()))
    raw_capture_sha = capture_bundle_fingerprint(row_file_digests)
    fingerprint_input = json.dumps(
        {"featureVersion": FEATURE_VERSION, "sourceSha256": expected_sha,
         "exporterSourceSha256": exporter_sha,
         "leanContextFingerprint": expected_context,
         "rawCaptureSha256": raw_capture_sha,
         "features": feature_rows}, sort_keys=True, separators=(",", ":"),
    )
    dna_fingerprint = hashlib.sha256(fingerprint_input.encode("utf-8")).hexdigest()
    observed_leakage_count = row_counts.get("raw_infotree_projection_leakage.jsonl", 0)
    if observed_leakage_count != leakage_count:
        raise ValueError(
            f"{metadata_path}: leakage_count {leakage_count} differs from "
            f"projection leakage row count {observed_leakage_count}"
        )
    return {
        "schema": "info_geometry.infotree_structural_dna.v1",
        "featureVersion": FEATURE_VERSION,
        "artifactId": repo_relative_source,
        "module": metadata.get("module"),
        "sourceSha256": expected_sha,
        "leanContextFingerprint": expected_context,
        "rawRowFileSha256": dict(sorted(row_file_digests.items())),
        "rawCaptureSha256": raw_capture_sha,
        "captureStage": metadata.get("stage"),
        "exporterSourceSha256": exporter_sha,
        "captureLossless": fully_lossless,
        "leakageRowCount": leakage_count,
        "status": "structural_dna_candidate" if fully_lossless and not leakage_count
                  else "partial_structural_candidate_with_recorded_loss",
        "rowCounts": dict(sorted(row_counts.items())),
        "featureCount": len(feature_rows),
        "features": feature_rows,
        "dnaFingerprint": dna_fingerprint,
        "authority": "source-bound structural features; not semantic archetypes or theorem identity",
    }


def extract_tree(exports_root: Path, *, repo_root: Path = ROOT) -> list[dict[str, Any]]:
    """Read per-file exports once each and reject duplicate source captures."""
    metadata_paths = sorted(
        path for path in exports_root.rglob("metadata.json")
        if "merged" not in path.relative_to(exports_root).parts
    )
    results: list[dict[str, Any]] = []
    seen_sources: dict[str, str] = {}
    for metadata_path in metadata_paths:
        result = extract_one(metadata_path.parent, repo_root=repo_root)
        source = result["artifactId"]
        if source in seen_sources:
            raise ValueError(
                f"duplicate current-source capture for {source}: "
                f"{seen_sources[source]} and {metadata_path.parent}"
            )
        seen_sources[source] = str(metadata_path.parent)
        results.append(result)
    return results


def _rejection_record(metadata_path: Path, exports_root: Path, repo_root: Path,
                      error: Exception) -> dict[str, Any]:
    """Describe an excluded capture without exposing feature or payload data."""
    try:
        metadata = json.loads(metadata_path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        metadata = {}
    provenance = metadata.get("sourceProvenance")
    provenance = provenance if isinstance(provenance, dict) else {}
    source_value = provenance.get("sourcePath")
    artifact_id = None
    if isinstance(source_value, str) and source_value:
        source = Path(source_value)
        if not source.is_absolute():
            source = repo_root / source
        try:
            artifact_id = source.resolve().relative_to(repo_root.resolve()).as_posix()
        except (OSError, ValueError):
            artifact_id = None

    message = str(error)
    if "exporter source receipt" in message:
        reason = "exporter_source_missing_or_stale"
    elif "toolchain/olean context differs" in message:
        reason = "stale_lean_context"
    elif "source changed while context provenance" in message:
        reason = "source_changed_during_context_check"
    elif "current source digest does not match" in message:
        reason = "stale_source_digest"
    elif "loss audit" in message:
        reason = "loss_audit_not_passed"
    elif "no source provenance" in message:
        reason = "source_provenance_missing"
    elif isinstance(error, OSError):
        reason = "capture_file_unavailable"
    else:
        reason = "invalid_capture"
    try:
        capture_dir = metadata_path.parent.resolve().relative_to(exports_root.resolve()).as_posix()
    except (OSError, ValueError):
        capture_dir = None
    return {
        "artifactId": artifact_id,
        "captureDirectory": capture_dir,
        "reason": reason,
        "errorType": type(error).__name__,
        "reportedSourceSha256": provenance.get("sourceSha256"),
        "reportedLeanContextFingerprint": provenance.get("leanContextFingerprint"),
        "reportedExporterSourceSha256": provenance.get("exporterSourceSha256"),
    }


def extract_tree_audited(exports_root: Path, *, repo_root: Path = ROOT
                         ) -> tuple[list[dict[str, Any]], list[dict[str, Any]]]:
    """Return valid DNA records and explicit rejections for the same export set.

    Rejected captures never become feature rows. Duplicate accepted captures
    remain fatal because they make the current source-to-capture join ambiguous.
    """
    metadata_paths = sorted(
        path for path in exports_root.rglob("metadata.json")
        if "merged" not in path.relative_to(exports_root).parts
    )
    records: list[dict[str, Any]] = []
    rejected: list[dict[str, Any]] = []
    seen_sources: dict[str, str] = {}
    for metadata_path in metadata_paths:
        try:
            result = extract_one(metadata_path.parent, repo_root=repo_root)
        except (OSError, ValueError) as error:
            rejected.append(_rejection_record(metadata_path, exports_root, repo_root, error))
            continue
        source = result["artifactId"]
        if source in seen_sources:
            raise ValueError(
                f"duplicate current-source capture for {source}: "
                f"{seen_sources[source]} and {metadata_path.parent}"
            )
        seen_sources[source] = str(metadata_path.parent)
        records.append(result)
    return records, rejected


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("exports_root", type=Path)
    parser.add_argument("--repo-root", type=Path, default=ROOT)
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument("--rejections-out", type=Path,
                        help="Write structured exclusions and continue past stale/invalid captures")
    args = parser.parse_args()
    if args.rejections_out:
        records, rejections = extract_tree_audited(args.exports_root, repo_root=args.repo_root)
    else:
        records, rejections = extract_tree(args.exports_root, repo_root=args.repo_root), []
    args.out.parent.mkdir(parents=True, exist_ok=True)
    with args.out.open("w", encoding="utf-8") as stream:
        for record in records:
            stream.write(json.dumps(record, sort_keys=True, ensure_ascii=False) + "\n")
    if args.rejections_out:
        args.rejections_out.parent.mkdir(parents=True, exist_ok=True)
        args.rejections_out.write_text(json.dumps({
            "schema": "info_geometry.infotree_dna_rejection_report.v1",
            "rejectionCount": len(rejections),
            "rejections": rejections,
            "authority": "excluded captures only; rejected records contribute no DNA features",
        }, sort_keys=True, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({
        "schema": "info_geometry.infotree_structural_dna_manifest.v1",
        "sourceCount": len(records),
        "featureRows": sum(int(record["featureCount"]) for record in records),
        "partialCaptureCount": sum(record["status"] != "structural_dna_candidate" for record in records),
        "rejectedCaptureCount": len(rejections),
        "output": str(args.out),
        "rejectionsOutput": str(args.rejections_out) if args.rejections_out else None,
    }, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
