#!/usr/bin/env python3
"""Bind one current-source snapshot to InfoTree DNA and Git fossil evidence.

The manifest is a deterministic receipt over current Lean source identities,
validated per-file structural DNA, missing capture coverage, and an optional
Git path-fossil overlay. It never synthesizes historical source or theorem DNA.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import sys
from typing import Any

# Support the documented file-path CLI as well as module execution. A direct
# ``python tools/repository_evolution/generation_manifest.py`` invocation puts
# this file's directory, not the repository root, at ``sys.path[0]``.
REPO_ROOT = Path(__file__).resolve().parents[2]
DEFAULT_REPO_ROOT = REPO_ROOT
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from tools.repository_evolution.git_fossil_overlay import _generation_id
from tools.repository_evolution.infotree_dna import (
    FEATURE_VERSION,
    ROW_FILES,
    capture_bundle_fingerprint,
)


MAP_SCHEMA = "info_geometry.refactoring_map.v1"
DNA_SCHEMA = "info_geometry.infotree_structural_dna.v1"
MANIFEST_SCHEMA = "info_geometry.current_source_generation_manifest.v2"
def _canonical_sha256(value: Any) -> str:
    payload = json.dumps(value, sort_keys=True, ensure_ascii=False,
                         separators=(",", ":")).encode("utf-8")
    return hashlib.sha256(payload).hexdigest()


def _is_sha256(value: Any) -> bool:
    if not isinstance(value, str) or len(value) != 64:
        return False
    try:
        int(value, 16)
    except ValueError:
        return False
    return value == value.lower()


def _complete_changed_path_set(snapshot: dict[str, Any]) -> list[str]:
    """Read a complete, self-consistent changed-path set from a source map."""
    changed = snapshot.get("changedPathsDuringScan")
    if changed is None:
        # Compatibility with older maps is safe only when the legacy sample is
        # itself complete; truncated samples cannot certify a selected scope.
        changed = snapshot.get("changedPathSampleDuringScan")
    count = snapshot.get("changedPathCountDuringScan")
    if (isinstance(count, bool) or not isinstance(count, int) or count < 0
            or not isinstance(changed, list)
            or any(not isinstance(path, str) or not path for path in changed)
            or len(changed) != count or len(set(changed)) != count):
        raise ValueError(
            "cannot verify selected scope: scanner omitted changed paths or supplied an incomplete set"
        )
    if changed != sorted(changed):
        raise ValueError("scanner changed paths are not in canonical order")
    declared_digest = snapshot.get("changedPathSetSha256")
    if declared_digest is not None:
        observed_digest = hashlib.sha256(json.dumps(
            changed, ensure_ascii=False, separators=(",", ":")
        ).encode("utf-8")).hexdigest()
        if declared_digest != observed_digest:
            raise ValueError("scanner changed-path-set digest mismatch")
    return changed


def _read_json(path: Path) -> dict[str, Any]:
    import gzip

    opener = gzip.open if path.suffix == ".gz" else open
    with opener(path, "rt", encoding="utf-8") as stream:
        value = json.load(stream)
    if not isinstance(value, dict):
        raise ValueError(f"{path}: expected a JSON object")
    return value


def _read_jsonl(path: Path) -> list[dict[str, Any]]:
    rows = []
    with path.open("r", encoding="utf-8") as stream:
        for number, line in enumerate(stream, 1):
            if not line.strip():
                continue
            try:
                row = json.loads(line)
            except json.JSONDecodeError as exc:
                raise ValueError(f"{path}:{number}: invalid JSON") from exc
            if not isinstance(row, dict):
                raise ValueError(f"{path}:{number}: expected a JSON object")
            rows.append(row)
    return rows


def _validate_dna_record(record: dict[str, Any], path: str,
                         expected_source_sha: str) -> None:
    if record.get("schema") != DNA_SCHEMA:
        raise ValueError(f"unsupported InfoTree DNA schema for {path}")
    if record.get("featureVersion") != FEATURE_VERSION:
        raise ValueError(f"unsupported InfoTree DNA feature version for {path}")
    if record.get("artifactId") != path:
        raise ValueError(f"InfoTree DNA artifact identity differs for {path}")
    if record.get("sourceSha256") != expected_source_sha:
        raise ValueError(f"InfoTree DNA source digest differs from current source for {path}")
    context = record.get("leanContextFingerprint")
    exporter_sha = record.get("exporterSourceSha256")
    if not _is_sha256(exporter_sha):
        raise ValueError(f"InfoTree DNA has an invalid exporter source fingerprint for {path}")
    capture_sha = record.get("rawCaptureSha256")
    features = record.get("features")
    row_hashes = record.get("rawRowFileSha256")
    if not _is_sha256(context):
        raise ValueError(f"InfoTree DNA has an invalid Lean context fingerprint for {path}")
    if not _is_sha256(capture_sha):
        raise ValueError(f"InfoTree DNA has an invalid raw-capture fingerprint for {path}")
    if not isinstance(row_hashes, dict) or any(
            not isinstance(name, str) or name not in ROW_FILES or not _is_sha256(digest)
            for name, digest in row_hashes.items()):
        raise ValueError(f"InfoTree DNA has invalid raw row-file digests for {path}")
    if (record.get("featureVersion") == FEATURE_VERSION
            and "raw_infotree_roots.jsonl" not in row_hashes):
        raise ValueError(f"InfoTree DNA v3 is missing its required roots-file digest for {path}")
    if (record.get("featureVersion") == FEATURE_VERSION
            and "raw_infotree_projection_leakage.jsonl" not in row_hashes):
        raise ValueError(
            f"InfoTree DNA v3 is missing its required projection-leakage digest for {path}"
        )
    if capture_bundle_fingerprint(row_hashes) != capture_sha:
        raise ValueError(f"InfoTree DNA raw-capture fingerprint does not match row-file hashes for {path}")
    if not isinstance(features, dict):
        raise ValueError(f"InfoTree DNA features must be an object for {path}")
    for name, count in features.items():
        if not isinstance(name, str) or isinstance(count, bool) or not isinstance(count, int) or count < 0:
            raise ValueError(f"InfoTree DNA has an invalid feature count for {path}")
    lossless = record.get("captureLossless")
    leakage_count = record.get("leakageRowCount")
    if not isinstance(lossless, bool):
        raise ValueError(f"InfoTree DNA has invalid capture-loss status for {path}")
    if isinstance(leakage_count, bool) or not isinstance(leakage_count, int) or leakage_count < 0:
        raise ValueError(f"InfoTree DNA has invalid leakage count for {path}")
    expected_status = ("structural_dna_candidate" if lossless and leakage_count == 0
                       else "partial_structural_candidate_with_recorded_loss")
    if record.get("status") != expected_status:
        raise ValueError(f"InfoTree DNA status disagrees with capture-loss evidence for {path}")
    fingerprint_input = {
        "featureVersion": FEATURE_VERSION,
        "sourceSha256": expected_source_sha,
        "leanContextFingerprint": context,
        "exporterSourceSha256": exporter_sha,
        "rawCaptureSha256": capture_sha,
        "features": features,
    }
    if record.get("dnaFingerprint") != _canonical_sha256(fingerprint_input):
        raise ValueError(f"InfoTree DNA fingerprint does not verify for {path}")


def _report_source_path(value: Any) -> str | None:
    """Normalize a batch-report path only when it points inside this checkout."""
    if not isinstance(value, str) or not value.strip() or value.startswith("<"):
        return None
    path = Path(value)
    if path.is_absolute():
        try:
            return path.resolve().relative_to(REPO_ROOT.resolve()).as_posix()
        except (OSError, ValueError):
            return None
    normalized = Path(value)
    if normalized.is_absolute() or ".." in normalized.parts:
        return None
    return normalized.as_posix()


def _capture_diagnostics(
        reports: list[dict[str, Any]], expected: dict[str, str],
        observed: dict[str, dict[str, Any]],
        rejection_reports: list[dict[str, Any]] | None = None) -> dict[str, Any]:
    """Summarize attempts without promoting batch success to current DNA."""
    by_source: dict[str, list[dict[str, Any]]] = {}
    status_counts: dict[str, int] = {}
    rejection_reason_counts: dict[str, int] = {}
    out_of_inventory = 0
    total_attempts = 0
    total_rejections = 0
    for report in reports:
        if report.get("schema") != "info_geometry.raw_infotree_batch_export_report.v1":
            raise ValueError("unsupported RawInfoTree batch report schema")
        results = report.get("results")
        if not isinstance(results, list):
            raise ValueError("RawInfoTree batch report must contain a results list")
        for result in results:
            if not isinstance(result, dict):
                raise ValueError("RawInfoTree batch report result must be an object")
            source = _report_source_path(result.get("file"))
            if source is None:
                out_of_inventory += 1
                continue
            if source not in expected:
                out_of_inventory += 1
                continue
            status = result.get("status")
            if not isinstance(status, str) or not status:
                raise ValueError(f"RawInfoTree batch result has no status for {source}")
            source_provenance = result.get("source_provenance")
            source_provenance = source_provenance if isinstance(source_provenance, dict) else {}
            reported_sha = result.get("source_sha256") or source_provenance.get("sourceSha256")
            source_matches = (reported_sha == expected[source]["sourceSha256"]
                              if _is_sha256(reported_sha) else None)
            attempt = {
                "reportedStatus": status,
                "sourceDigestMatch": source_matches,
                "dnaAccepted": source in observed,
            }
            context = source_provenance.get("leanContextFingerprint")
            if isinstance(context, str) and context:
                attempt["captureContextFingerprint"] = context
            by_source.setdefault(source, []).append(attempt)
            status_counts[status] = status_counts.get(status, 0) + 1
            total_attempts += 1

    for report in rejection_reports or []:
        if report.get("schema") != "info_geometry.infotree_dna_rejection_report.v1":
            raise ValueError("unsupported InfoTree DNA rejection report schema")
        rejections = report.get("rejections")
        if not isinstance(rejections, list):
            raise ValueError("InfoTree DNA rejection report must contain a rejections list")
        if report.get("rejectionCount") != len(rejections):
            raise ValueError("InfoTree DNA rejection count does not match its entries")
        for rejection in rejections:
            if not isinstance(rejection, dict):
                raise ValueError("InfoTree DNA rejection entry must be an object")
            source = rejection.get("artifactId")
            reason = rejection.get("reason")
            if not isinstance(source, str) or not isinstance(reason, str) or not reason:
                raise ValueError("InfoTree DNA rejection must identify artifactId and reason")
            if source not in expected:
                out_of_inventory += 1
                continue
            by_source.setdefault(source, []).append({
                "reportedStatus": "dna_rejected",
                "rejectionReason": reason,
                "sourceDigestMatch": (
                    rejection.get("reportedSourceSha256") == expected[source]["sourceSha256"]
                    if _is_sha256(rejection.get("reportedSourceSha256")) else None
                ),
                "dnaAccepted": False,
            })
            rejection_reason_counts[reason] = rejection_reason_counts.get(reason, 0) + 1
            total_rejections += 1

    missing_diagnostics = []
    for source in sorted(set(expected) - set(observed)):
        attempts = by_source.get(source, [])
        rejected_reasons = {item.get("rejectionReason") for item in attempts}
        owner_status = expected[source].get("ownerStatus")
        if not attempts:
            if owner_status == "uncertain_module_not_in_lake_target_index":
                reason = "source_not_in_lake_target_index"
            elif owner_status == "uncertain_no_root_reachability":
                reason = "module_not_reachable_from_lake_root"
            else:
                reason = "no_batch_attempt_recorded"
        elif any(item["dnaAccepted"] for item in attempts):
            reason = "internal_coverage_mismatch"
        elif "stale_lean_context" in rejected_reasons:
            reason = "lean_context_rejected"
        elif "stale_source_digest" in rejected_reasons:
            reason = "source_digest_rejected"
        elif any(item["reportedStatus"] == "ok" and item["sourceDigestMatch"] is True
                 for item in attempts):
            reason = "export_succeeded_but_no_current_dna_record"
        elif any(item["sourceDigestMatch"] is False for item in attempts):
            reason = "capture_source_digest_is_stale"
        else:
            reason = "all_recorded_attempts_failed_or_unbound"
        missing_diagnostics.append({
            "artifactId": source,
            "reason": reason,
            "attempts": sorted(attempts, key=lambda item: (
                item["reportedStatus"], str(item["sourceDigestMatch"]),
                item.get("captureContextFingerprint", ""),
            )),
        })
    return {
        "batchReportCount": len(reports),
        "rejectionReportCount": len(rejection_reports or []),
        "attemptCount": total_attempts,
        "rejectedCaptureCount": total_rejections,
        "attemptStatusCounts": dict(sorted(status_counts.items())),
        "rejectionReasonCounts": dict(sorted(rejection_reason_counts.items())),
        "outOfInventoryAttemptCount": out_of_inventory,
        "missingSourcesWithAttempts": sum(bool(row["attempts"])
                                           for row in missing_diagnostics),
        "missingSourceDiagnostics": missing_diagnostics,
        "authority": "attempt diagnostics only; only validated DNA rows count as captured coverage",
    }


def build_current_source_generation_manifest(
        refactoring_map: dict[str, Any], dna_records: list[dict[str, Any]],
        fossil_overlay: dict[str, Any] | None = None,
        batch_reports: list[dict[str, Any]] | None = None,
        rejection_reports: list[dict[str, Any]] | None = None,
        scope_artifacts: list[str] | None = None,
        repo_root: Path = DEFAULT_REPO_ROOT) -> dict[str, Any]:
    """Create a stable, self-digested manifest; incomplete capture stays explicit."""
    if refactoring_map.get("schema") != MAP_SCHEMA:
        raise ValueError(f"expected {MAP_SCHEMA}")
    snapshot = refactoring_map.get("sourceSnapshot") or {}
    provenance = refactoring_map.get("analysisProvenance") or {}
    globally_consistent = snapshot.get("worktreeConsistentDuringScan") is True
    if not globally_consistent and not scope_artifacts:
        raise ValueError("refusing an inconsistent current-source snapshot without selected scope")
    if provenance.get("analysisInputsConsistentDuringScan") is not True:
        raise ValueError("refusing inconsistent scanner/Lake provenance")
    source_snapshot_sha = snapshot.get("pathContentManifestSha256")
    if not _is_sha256(source_snapshot_sha):
        raise ValueError("source map lacks a valid path-content manifest digest")
    git_head = snapshot.get("gitHead")
    if (not isinstance(git_head, str) or len(git_head) != 40
            or any(character not in "0123456789abcdef" for character in git_head)):
        raise ValueError("source map lacks a full Git HEAD identity")
    for field, value in (("scannerSourceSha256", provenance.get("scannerSourceSha256")),
                         ("lakeManifestSha256", provenance.get("lakeManifestSha256")),
                         ("filesystemTopologySha256", snapshot.get("filesystemTopologySha256"))):
        if not _is_sha256(value):
            raise ValueError(f"source map lacks valid {field} provenance")

    source_rows = [row for row in refactoring_map.get("files", [])
                   if isinstance(row, dict) and row.get("role") == "lean_source"]
    expected: dict[str, dict[str, Any]] = {}
    for row in source_rows:
        path, source_sha = row.get("path"), row.get("contentSha256")
        if not isinstance(path, str) or not _is_sha256(source_sha):
            raise ValueError("Lean source inventory has a missing path or invalid content digest")
        if path in expected:
            raise ValueError(f"duplicate Lean source inventory path {path}")
        build_targets = row.get("buildTargets", [])
        if (not isinstance(build_targets, list)
                or any(not isinstance(target, str) for target in build_targets)):
            raise ValueError(f"Lean source has invalid Lake build targets for {path}")
        owner_status = row.get("ownerStatus", "not_recorded")
        if not isinstance(owner_status, str):
            raise ValueError(f"Lean source has invalid owner status for {path}")
        module = row.get("module")
        if module is not None and not isinstance(module, str):
            raise ValueError(f"Lean source has invalid module identity for {path}")
        expected[path] = {
            "sourceSha256": source_sha,
            "module": module,
            "buildTargets": sorted(set(build_targets)),
            "ownerStatus": owner_status,
        }

    if scope_artifacts is not None:
        if (not isinstance(scope_artifacts, list) or not scope_artifacts
                or any(not isinstance(path, str) or not path for path in scope_artifacts)
                or len(scope_artifacts) != len(set(scope_artifacts))):
            raise ValueError("selected scope must be a non-empty unique artifact-path list")
        unknown_scope = sorted(set(scope_artifacts) - set(expected))
        if unknown_scope:
            raise ValueError(f"selected scope contains non-current Lean sources: {unknown_scope[:5]}")
        expected = {path: expected[path] for path in sorted(scope_artifacts)}
        root = Path(os.path.abspath(os.fspath(repo_root)))
        live_hashes: dict[str, str] = {}
        for path, source in expected.items():
            candidate = Path(os.path.abspath(os.fspath(root / path)))
            try:
                candidate.relative_to(root)
            except ValueError as exc:
                raise ValueError(f"selected source path escapes repository root: {path}") from exc
            if not candidate.is_file():
                raise ValueError(f"selected current Lean source is missing: {path}")
            resolved = candidate.resolve()
            try:
                resolved.relative_to(root.resolve())
            except ValueError as exc:
                raise ValueError(f"selected source symlink escapes repository root: {path}") from exc
            source_bytes = candidate.read_bytes()
            actual_sha = hashlib.sha256(source_bytes).hexdigest()
            if actual_sha != source["sourceSha256"]:
                raise ValueError(f"selected source digest differs from map for {path}")
            if hashlib.sha256(candidate.read_bytes()).hexdigest() != actual_sha:
                raise ValueError(f"selected source changed while verifying scope: {path}")
            live_hashes[path] = actual_sha

        changed_paths: list[str] = []
        changed_disjoint = True
        if not globally_consistent:
            changed_paths = _complete_changed_path_set(snapshot)
            overlap = set(changed_paths) & set(expected)
            if overlap:
                changed_disjoint = False
                raise ValueError(
                    "selected source scope intersects paths changed during scan: "
                    + ", ".join(sorted(overlap)[:5])
                )
        manifest_scope = {
            "kind": "selected_lean_source_scope",
            "artifactIds": sorted(expected),
            "sourceSha256ByArtifact": live_hashes,
            "globalSnapshotConsistent": globally_consistent,
            "changedPathsDuringScan": changed_paths,
            "scopeDisjointFromChangedPaths": changed_disjoint,
        }
    else:
        manifest_scope = {
            "kind": "full_current_lean_inventory",
            "artifactCount": len(expected),
            "globalSnapshotConsistent": True,
            "scopeDisjointFromChangedPaths": True,
        }

    observed: dict[str, dict[str, Any]] = {}
    for record in dna_records:
        path = record.get("artifactId")
        if not isinstance(path, str):
            raise ValueError("InfoTree DNA record has no artifactId")
        if path in observed:
            raise ValueError(f"duplicate InfoTree DNA record for {path}")
        if path not in expected:
            raise ValueError(f"InfoTree DNA references a non-current Lean source {path}")
        _validate_dna_record(record, path, expected[path]["sourceSha256"])
        observed[path] = record

    missing = sorted(set(expected) - set(observed))
    source_inventory_sha = _canonical_sha256([
        {"artifactId": path, **expected[path]}
        for path in sorted(expected)
    ])
    build_owner_status_counts: dict[str, int] = {}
    target_expected_counts: dict[str, int] = {}
    target_captured_counts: dict[str, int] = {}
    expected_without_target = 0
    captured_without_target = 0
    for source in expected.values():
        status = source["ownerStatus"]
        build_owner_status_counts[status] = build_owner_status_counts.get(status, 0) + 1
        targets = source["buildTargets"]
        if not targets:
            expected_without_target += 1
            continue
        for target in targets:
            target_expected_counts[target] = target_expected_counts.get(target, 0) + 1
    for path in observed:
        targets = expected[path]["buildTargets"]
        if not targets:
            captured_without_target += 1
            continue
        for target in targets:
            target_captured_counts[target] = target_captured_counts.get(target, 0) + 1
    target_capture_coverage = {
        target: {
            "expectedSourceCount": expected_count,
            "capturedSourceCount": target_captured_counts.get(target, 0),
            "missingSourceCount": expected_count - target_captured_counts.get(target, 0),
            "coverageRatio": target_captured_counts.get(target, 0) / expected_count,
        }
        for target, expected_count in sorted(target_expected_counts.items())
    }
    unindexed_sources = sorted(
        path for path, source in expected.items()
        if source["ownerStatus"] == "uncertain_module_not_in_lake_target_index"
    )
    unreachable_modules = sorted(
        path for path, source in expected.items()
        if source["ownerStatus"] == "uncertain_no_root_reachability"
    )
    dna_rows_sha = _canonical_sha256([
        observed[path] for path in sorted(observed)
    ])
    capture_audit = _capture_diagnostics(
        batch_reports or [], expected, observed, rejection_reports
    )
    overlay_summary = None
    if fossil_overlay is not None:
        if fossil_overlay.get("schema") != "info_geometry.git_fossil_overlay_manifest.v1":
            raise ValueError("unsupported Git-fossil overlay manifest")
        if fossil_overlay.get("pathContentManifestSha256") != source_snapshot_sha:
            raise ValueError("Git-fossil overlay belongs to a different source snapshot")
        if fossil_overlay.get("gitHead") != snapshot.get("gitHead"):
            raise ValueError("Git-fossil overlay belongs to a different HEAD")
        if fossil_overlay.get("sourceCount") != len(observed):
            raise ValueError("Git-fossil overlay source coverage differs from InfoTree DNA")
        for field in ("generationId", "gitPathEventsSha256", "nodeLinksSha256",
                      "sourceLineFossilsSha256", "declarationLineFossilLinksSha256",
                      "sourceLineageFeaturesSha256"):
            value = fossil_overlay.get(field)
            if field.endswith("Sha256") and not _is_sha256(value):
                raise ValueError(f"Git-fossil overlay has invalid {field}")
            if field == "generationId" and not _is_sha256(value):
                raise ValueError("Git-fossil overlay has invalid generationId")
        expected_overlay_id = _generation_id(snapshot, provenance)
        if fossil_overlay.get("generationId") != expected_overlay_id:
            raise ValueError("Git-fossil overlay generation identity differs from source map")
        lineage_features = fossil_overlay.get("sourceLineageFeaturesByPath")
        if not isinstance(lineage_features, dict) or set(lineage_features) != set(observed):
            raise ValueError("Git-fossil overlay lineage features do not cover captured DNA sources")
        if _canonical_sha256(lineage_features) != fossil_overlay.get("sourceLineageFeaturesSha256"):
            raise ValueError("Git-fossil overlay lineage feature digest mismatch")
        for path, features in lineage_features.items():
            if (not isinstance(features, dict)
                    or features.get("schema") != "info_geometry.source_lineage_features.v1"
                    or features.get("generationId") != expected_overlay_id
                    or features.get("historyRevision") != git_head
                    or features.get("sourcePath") != path
                    or features.get("sourceSha256") != expected[path]["sourceSha256"]):
                raise ValueError(f"invalid Git line-origin feature provenance for {path}")
        overlay_summary = {
            "schema": fossil_overlay["schema"],
            "generationId": fossil_overlay["generationId"],
            "gitPathEventsSha256": fossil_overlay["gitPathEventsSha256"],
            "gitPathEventCount": fossil_overlay.get("gitPathEventCount"),
            "nodeLinksSha256": fossil_overlay["nodeLinksSha256"],
            "nodeLinkCount": fossil_overlay.get("nodeLinkCount"),
            "sourceLineFossilsSha256": fossil_overlay["sourceLineFossilsSha256"],
            "sourceLineFossilSpanCount": fossil_overlay.get("sourceLineFossilSpanCount"),
            "declarationLineFossilLinksSha256": fossil_overlay[
                "declarationLineFossilLinksSha256"
            ],
            "declarationLineFossilLinkCount": fossil_overlay.get(
                "declarationLineFossilLinkCount"
            ),
            "declarationLineFossilEdgeCount": fossil_overlay.get(
                "declarationLineFossilEdgeCount"
            ),
            "sourceLineageFeaturesSha256": fossil_overlay["sourceLineageFeaturesSha256"],
            "sourceLineageFeatureSourceCount": len(lineage_features),
        }

    body = {
        "schema": MANIFEST_SCHEMA,
        "sourceGenerationId": _canonical_sha256({
            "gitHead": git_head,
            "sourceSnapshotSha256": source_snapshot_sha,
            "filesystemTopologySha256": snapshot["filesystemTopologySha256"],
            "scannerSourceSha256": provenance["scannerSourceSha256"],
            "lakeManifestSha256": provenance["lakeManifestSha256"],
            "manifestScope": manifest_scope,
        }),
        "gitHead": git_head,
        "sourceSnapshotSha256": source_snapshot_sha,
        "filesystemTopologySha256": snapshot["filesystemTopologySha256"],
        "scannerSourceSha256": provenance["scannerSourceSha256"],
        "lakeManifestSha256": provenance["lakeManifestSha256"],
        "manifestScope": manifest_scope,
        "sourceInventorySha256": source_inventory_sha,
        "expectedLeanSourceCount": len(expected),
        "lakeOwnerStatusCounts": dict(sorted(build_owner_status_counts.items())),
        "lakeBuildTargetCaptureCoverage": {
            "targetCount": len(target_capture_coverage),
            "targets": target_capture_coverage,
            "sourcesWithoutBuildTargets": {
                "expectedSourceCount": expected_without_target,
                "capturedSourceCount": captured_without_target,
                "missingSourceCount": expected_without_target - captured_without_target,
            },
            "interpretation": (
                "per-target counts are overlapping when a Lean source belongs to multiple "
                "Lake targets; sources without targets are reported separately"
            ),
        },
        "unindexedLeanSources": unindexed_sources,
        "unreachableLeanModules": unreachable_modules,
        "capturedLeanSourceCount": len(observed),
        "missingLeanSources": missing,
        "coverageRatio": len(observed) / len(expected) if expected else 1.0,
        "coverageStatus": "complete" if not missing else "partial_missing_captures",
        "infotreeFeatureVersion": FEATURE_VERSION,
        "infotreeDnaRowsSha256": dna_rows_sha,
        "partialCaptureCount": sum(
            observed[path].get("status") != "structural_dna_candidate"
            for path in observed
        ),
        "leakageRowCount": sum(
            int(observed[path].get("leakageRowCount", 0) or 0)
            for path in observed
        ),
        "captureAttemptAudit": capture_audit,
        "gitFossilOverlay": overlay_summary,
        "authority": "current-source and compiler-capture coverage receipt; Git relations remain path-level fossils",
    }
    return {**body, "manifestSha256": _canonical_sha256(body)}


def validate_current_source_generation_manifest(
        refactoring_map: dict[str, Any], dna_records: list[dict[str, Any]],
        manifest: dict[str, Any], fossil_overlay: dict[str, Any] | None = None,
        batch_reports: list[dict[str, Any]] | None = None,
        rejection_reports: list[dict[str, Any]] | None = None,
        repo_root: Path = DEFAULT_REPO_ROOT) -> None:
    """Recompute the receipt from inputs and reject stale or edited manifests."""
    manifest_scope = manifest.get("manifestScope")
    scope_artifacts = None
    if isinstance(manifest_scope, dict) and manifest_scope.get("kind") == "selected_lean_source_scope":
        scope_artifacts = manifest_scope.get("artifactIds")
    expected = build_current_source_generation_manifest(
        refactoring_map, dna_records, fossil_overlay, batch_reports, rejection_reports,
        scope_artifacts, repo_root,
    )
    if manifest != expected:
        raise ValueError("current-source generation manifest does not match its inputs")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("refactoring_map", type=Path)
    parser.add_argument("infotree_dna", type=Path)
    parser.add_argument("--fossil-overlay-manifest", type=Path)
    parser.add_argument("--batch-report", type=Path, action="append", default=[],
                        help="RawInfoTree batch report; may be repeated to retain retry outcomes")
    parser.add_argument("--dna-rejections", type=Path, action="append", default=[],
                        help="Audited InfoTree extraction rejection report; may be repeated")
    parser.add_argument("--scope-artifact", action="append", default=None,
                        help="Bind an explicit current Lean source scope; repeat for multiple paths")
    parser.add_argument("--repo-root", type=Path, default=DEFAULT_REPO_ROOT)
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()
    source_map = _read_json(args.refactoring_map)
    dna_records = _read_jsonl(args.infotree_dna)
    overlay = (_read_json(args.fossil_overlay_manifest)
               if args.fossil_overlay_manifest else None)
    batch_reports = [_read_json(path) for path in args.batch_report]
    rejection_reports = [_read_json(path) for path in args.dna_rejections]
    manifest = build_current_source_generation_manifest(
        source_map, dna_records, overlay, batch_reports, rejection_reports,
        args.scope_artifact, args.repo_root,
    )
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(manifest, sort_keys=True, indent=2) + "\n",
                        encoding="utf-8")
    print(json.dumps({
        "sourceGenerationId": manifest["sourceGenerationId"],
        "manifestSha256": manifest["manifestSha256"],
        "expectedLeanSourceCount": manifest["expectedLeanSourceCount"],
        "capturedLeanSourceCount": manifest["capturedLeanSourceCount"],
        "coverageStatus": manifest["coverageStatus"],
    }, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
