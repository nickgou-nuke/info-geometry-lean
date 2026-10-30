#!/usr/bin/env python3
"""Create a stratified, source-bound queue for human taxonomy adjudication.

The queue carries observed scanner context and candidate source spans, but
never assigns labels. Its rows are review tasks, not training annotations.
"""
from __future__ import annotations

import argparse
import gzip
import hashlib
import json
import sys
from collections import Counter, defaultdict
from pathlib import Path
from typing import Any

_REPOSITORY_ROOT = Path(__file__).resolve().parents[2]
if str(_REPOSITORY_ROOT) not in sys.path:
    sys.path.insert(0, str(_REPOSITORY_ROOT))

from tools.infra.detect_archetypes import ARCHETYPE_SIGNATURES


MAP_SCHEMA = "info_geometry.refactoring_map.v1"
ROOT = Path(__file__).resolve().parents[2]
FACETS = ("artifact_role", "semantic_archetype")


def _read_json(path: Path) -> dict[str, Any]:
    opener = gzip.open if path.suffix == ".gz" else open
    with opener(path, "rt", encoding="utf-8") as stream:
        result = json.load(stream)
    if not isinstance(result, dict):
        raise ValueError(f"{path}: expected a JSON object")
    return result


def _read_jsonl(path: Path) -> list[dict[str, Any]]:
    rows = []
    with path.open("r", encoding="utf-8") as stream:
        for line_number, line in enumerate(stream, 1):
            if not line.strip():
                continue
            try:
                row = json.loads(line)
            except json.JSONDecodeError as exc:
                raise ValueError(f"{path}:{line_number}: invalid JSON") from exc
            if not isinstance(row, dict):
                raise ValueError(f"{path}:{line_number}: expected an object")
            rows.append(row)
    return rows


def _sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def _scan_changed_paths(snapshot: dict[str, Any], allow_scoped_review: bool) -> set[str]:
    """Return the complete scanner-reported changed-path set for scoped review.

    The opt-in does not make the scan globally consistent. It permits later
    per-task source-hash checks to establish a narrower review scope.
    """
    if snapshot.get("worktreeConsistentDuringScan") is True:
        return set()
    if not allow_scoped_review:
        raise ValueError("refusing an inconsistent source snapshot")
    changed_count = snapshot.get("changedPathCountDuringScan")
    changed_sample = snapshot.get("changedPathSampleDuringScan")
    if (isinstance(changed_count, bool) or not isinstance(changed_count, int)
            or changed_count < 0 or not isinstance(changed_sample, list)
            or any(not isinstance(path, str) or not path for path in changed_sample)
            or len(changed_sample) != changed_count
            or len(set(changed_sample)) != changed_count):
        raise ValueError("cannot scope review: scanner did not report every changed path")
    return set(changed_sample)


def _owner_group(row: dict[str, Any]) -> str:
    module = row.get("module")
    if isinstance(module, str) and module:
        return f"module:{module}"
    module_candidate = row.get("moduleCandidate")
    source_root = row.get("moduleCandidateSourceRoot")
    if (isinstance(module_candidate, str) and module_candidate
            and isinstance(source_root, str) and source_root):
        return f"module_candidate:{source_root}:{module_candidate}"
    owner_status = str(row.get("ownerStatus", ""))
    owner_is_uncertain = (owner_status.startswith(("uncertain", "unresolved")))
    owner = row.get("owner")
    if isinstance(owner, list) and not owner_is_uncertain:
        return "owner:" + ",".join(sorted(str(value) for value in owner))
    if (isinstance(owner, str) and owner and owner != "unresolved"
            and not owner_is_uncertain and not owner.startswith("unresolved_")):
        return f"owner:{owner}"
    return f"directory:{Path(str(row['path'])).parent.as_posix()}"


def _uncertainty_stratum(row: dict[str, Any]) -> str:
    fields = (row.get("status"), row.get("ownerStatus"), row.get("role"))
    return "uncertain" if any("uncertain" in str(value).lower() for value in fields) else "observed"


def _sample(candidates: list[dict[str, Any]], *, limit: int, max_per_owner: int,
            seed: str, eligible: Any = None) -> list[dict[str, Any]]:
    buckets: dict[tuple[str, str], list[dict[str, Any]]] = defaultdict(list)
    for row in candidates:
        key = (str(row.get("role", "unknown")), _uncertainty_stratum(row))
        buckets[key].append(row)
    for key, rows in buckets.items():
        rows.sort(key=lambda row: hashlib.sha256(
            f"{seed}\0{row['path']}".encode("utf-8")
        ).hexdigest())
    selected = []
    owner_counts: Counter[str] = Counter()
    cursors = {key: 0 for key in buckets}
    while len(selected) < limit:
        progressed = False
        for key in sorted(buckets):
            rows = buckets[key]
            while cursors[key] < len(rows):
                row = rows[cursors[key]]
                cursors[key] += 1
                group = _owner_group(row)
                if owner_counts[group] >= max_per_owner:
                    continue
                if eligible is not None and not eligible(row):
                    continue
                selected.append(row)
                owner_counts[group] += 1
                progressed = True
                break
            if len(selected) >= limit:
                break
        if not progressed:
            break
    return selected


def _source_spans(source_text: str, source_sha: str,
                  declarations: list[dict[str, Any]], *,
                  max_spans: int = 8) -> list[dict[str, Any]]:
    lines = source_text.splitlines()
    if not lines:
        return []
    candidates = []
    for declaration in declarations:
        line = declaration.get("line")
        if isinstance(line, int) and not isinstance(line, bool) and 1 <= line <= len(lines):
            start, end = max(1, line - 2), min(len(lines), line + 2)
            candidates.append((start, end, declaration))
    if not candidates:
        candidates = [(1, min(10, len(lines)), {})]
    spans = []
    seen = set()
    for start, end, declaration in sorted(candidates, key=lambda item: (item[0], item[1])):
        if (start, end) in seen:
            continue
        seen.add((start, end))
        spans.append({
            "startLine": start,
            "endLine": end,
            "sourceSha256": source_sha,
            "declarationKind": declaration.get("kind"),
            "declarationName": declaration.get("name"),
            "excerpt": "\n".join(lines[start - 1:end])[:700],
        })
        if len(spans) >= max_spans:
            break
    return spans


def build_adjudication_queue(report: dict[str, Any], repo_root: Path = ROOT, *,
                             limit: int = 80, max_per_owner: int = 3,
                             seed: str = "taxonomy-review-v1",
                             infotree_dna: list[dict[str, Any]] | None = None,
                             allow_scoped_review: bool = False,
                             ) -> tuple[list[dict[str, Any]], dict[str, Any]]:
    if report.get("schema") != MAP_SCHEMA:
        raise ValueError(f"expected {MAP_SCHEMA}")
    snapshot = report.get("sourceSnapshot") or {}
    provenance = report.get("analysisProvenance") or {}
    inventory_scope = snapshot.get("inventoryScope", "unspecified_inventory_scope")
    inventory_consistent = snapshot.get("worktreeConsistentDuringScan") is True
    whole_worktree_consistent = (
        inventory_consistent and inventory_scope == "repository_worktree_inventory"
    )
    selected_inventory_consistent = (
        inventory_consistent and inventory_scope == "explicit_path_selection"
    )
    unspecified_scope_consistent = (
        inventory_consistent
        and inventory_scope not in {
            "repository_worktree_inventory", "explicit_path_selection"
        }
    )
    if whole_worktree_consistent:
        consistency_status = "whole_worktree_consistent"
        source_snapshot_status = "whole_worktree_consistent"
        dependency_context_status = "whole_worktree_consistent"
    elif selected_inventory_consistent:
        consistency_status = "selected_inventory_paths_consistent"
        source_snapshot_status = "selected_inventory_paths_consistent"
        dependency_context_status = (
            "partial_inventory_consistent_dependency_context_truncated"
        )
    elif unspecified_scope_consistent:
        consistency_status = "inventory_scope_unspecified_selected_sources_hash_verified"
        source_snapshot_status = "inventory_scope_unspecified_selected_sources_hash_verified"
        dependency_context_status = "inventory_scope_unspecified_dependency_context_scope_unknown"
    else:
        consistency_status = "selected_source_hashes_verified_from_inconsistent_map"
        source_snapshot_status = "selected_source_hash_verified_from_inconsistent_map"
        dependency_context_status = "map_edges_from_scoped_scan_require_caution"
    changed_paths = _scan_changed_paths(snapshot, allow_scoped_review)
    if provenance.get("analysisInputsConsistentDuringScan") is not True:
        raise ValueError("refusing missing or unstable scanner/Lake provenance")
    if isinstance(limit, bool) or not isinstance(limit, int) or limit < 1:
        raise ValueError("limit must be a positive integer")
    if isinstance(max_per_owner, bool) or not isinstance(max_per_owner, int) or max_per_owner < 1:
        raise ValueError("max_per_owner must be a positive integer")
    if not isinstance(seed, str) or not seed:
        raise ValueError("seed must be a non-empty string")
    files = report.get("files")
    edges = report.get("dependencyEdges")
    declarations = report.get("leanDeclarationCandidates")
    if not isinstance(files, list) or not isinstance(edges, list) or not isinstance(declarations, list):
        raise ValueError("map requires files, dependencyEdges, and leanDeclarationCandidates")
    candidates = [row for row in files if isinstance(row, dict)
                  and isinstance(row.get("path"), str)
                  and isinstance(row.get("contentSha256"), str)]
    if len({row["path"] for row in candidates}) != len(candidates):
        raise ValueError("map contains duplicate candidate paths")
    candidate_count = len(candidates)
    all_files_by_path = {row["path"]: row for row in candidates}
    candidates = [row for row in candidates if row["path"] not in changed_paths]
    files_by_path = {row["path"]: row for row in candidates}
    dna_by_path: dict[str, dict[str, Any]] = {}
    for record in infotree_dna or []:
        if not isinstance(record, dict):
            raise ValueError("each InfoTree DNA record must be an object")
        artifact = record.get("artifactId")
        if not isinstance(artifact, str) or artifact not in all_files_by_path:
            raise ValueError(f"InfoTree DNA references an unknown map artifact: {artifact!r}")
        if record.get("sourceSha256") != all_files_by_path[artifact].get("contentSha256"):
            raise ValueError(f"InfoTree DNA source hash differs from map for {artifact}")
        if record.get("schema") != "info_geometry.infotree_structural_dna.v1":
            raise ValueError(f"unsupported InfoTree DNA schema for {artifact}")
        if artifact not in changed_paths:
            if artifact in dna_by_path:
                raise ValueError(f"duplicate InfoTree DNA record for {artifact}")
            dna_by_path[artifact] = record
    root = repo_root.resolve()
    source_cache: dict[str, tuple[bytes, str, str]] = {}
    unreviewable_text_count = 0
    stale_or_missing_source_count = 0
    stale_or_missing_source_paths: set[str] = set()
    source_hash_verified_count = 0

    def reviewable_source(row: dict[str, Any]) -> bool:
        nonlocal unreviewable_text_count, stale_or_missing_source_count
        nonlocal source_hash_verified_count
        artifact = row["path"]
        source_path = (root / artifact).resolve()
        try:
            source_path.relative_to(root)
        except ValueError as exc:
            raise ValueError(f"source path escapes repository root: {artifact}") from exc
        if not source_path.is_file():
            if allow_scoped_review:
                stale_or_missing_source_count += 1
                stale_or_missing_source_paths.add(artifact)
                return False
            raise ValueError(f"selected source is missing since map generation: {artifact}")
        raw = source_path.read_bytes()
        source_sha = _sha256(raw)
        if source_sha != row["contentSha256"]:
            if allow_scoped_review:
                stale_or_missing_source_count += 1
                stale_or_missing_source_paths.add(artifact)
                return False
            raise ValueError(f"selected source changed since map generation: {artifact}")
        source_hash_verified_count += 1
        if b"\0" in raw:
            unreviewable_text_count += 1
            return False
        try:
            text = raw.decode("utf-8")
        except UnicodeDecodeError:
            unreviewable_text_count += 1
            return False
        if not text.splitlines():
            unreviewable_text_count += 1
            return False
        source_cache[artifact] = (raw, text, source_sha)
        return True

    selected = _sample(candidates, limit=limit, max_per_owner=max_per_owner, seed=seed,
                       eligible=reviewable_source)
    declarations_by_path: dict[str, list[dict[str, Any]]] = defaultdict(list)
    for declaration in declarations:
        if isinstance(declaration, dict) and isinstance(declaration.get("sourcePath"), str):
            declarations_by_path[declaration["sourcePath"]].append(declaration)
    outgoing: dict[str, Counter[str]] = defaultdict(Counter)
    incoming: dict[str, Counter[str]] = defaultdict(Counter)
    changed_dependency_neighbors: dict[str, set[str]] = defaultdict(set)
    for edge in edges:
        if not isinstance(edge, dict):
            continue
        kind = str(edge.get("kind", "unknown"))
        if isinstance(edge.get("from"), str):
            outgoing[edge["from"]][kind] += 1
            if edge.get("to") in changed_paths and isinstance(edge.get("from"), str):
                changed_dependency_neighbors[edge["from"]].add(str(edge["to"]))
        if isinstance(edge.get("to"), str):
            incoming[edge["to"]][kind] += 1
            if edge.get("from") in changed_paths and isinstance(edge.get("to"), str):
                changed_dependency_neighbors[edge["to"]].add(str(edge["from"]))

    tasks = []
    for row in selected:
        artifact = row["path"]
        _raw, text, source_sha = source_cache[artifact]
        declarations_for_file = declarations_by_path.get(artifact, [])
        spans = _source_spans(text, source_sha, declarations_for_file)
        declaration_counts = Counter(str(item.get("kind", "unknown"))
                                     for item in declarations_for_file)
        observed_context = {
            "role": row.get("role"),
            "status": row.get("status"),
            "owner": row.get("owner"),
            "ownerStatus": row.get("ownerStatus"),
            "module": row.get("module"),
            "moduleCandidate": row.get("moduleCandidate"),
            "moduleCandidateSourceRoot": row.get("moduleCandidateSourceRoot"),
            "moduleCandidateStatus": row.get("moduleCandidateStatus"),
            "buildTargets": row.get("buildTargets", []),
            "sizeBytes": row.get("sizeBytes"),
            "gitPathHistory": row.get("gitPathHistory"),
            "incomingDependencyKinds": dict(sorted(incoming[artifact].items())),
            "outgoingDependencyKinds": dict(sorted(outgoing[artifact].items())),
            "dependencyContextStatus": dependency_context_status,
            "changedDependencyNeighbors": sorted(changed_dependency_neighbors[artifact]),
            "declarationKindCounts": dict(sorted(declaration_counts.items())),
            "infotreeDNA": ({
                "featureVersion": dna_by_path[artifact].get("featureVersion"),
                "dnaFingerprint": dna_by_path[artifact].get("dnaFingerprint"),
                "features": dna_by_path[artifact].get("features", {}),
                "captureLossless": dna_by_path[artifact].get("captureLossless"),
                "leakageRowCount": dna_by_path[artifact].get("leakageRowCount"),
                "evidenceStatus": "source_bound_structural_candidate",
            } if artifact in dna_by_path else None),
        }
        for facet in FACETS:
            identity = f"{snapshot.get('pathContentManifestSha256')}\0{artifact}\0{facet}"
            task_id = hashlib.sha256(identity.encode("utf-8")).hexdigest()
            tasks.append({
                "schema": "info_geometry.taxonomy_adjudication_task.v2",
                "taskId": task_id,
                "artifactId": artifact,
                "sourceSha256": source_sha,
                "sourceSnapshotSha256": snapshot.get("pathContentManifestSha256"),
                "sourceSnapshotStatus": source_snapshot_status,
                "inventoryScope": inventory_scope,
                "facet": facet,
                "reviewStatus": "pending_human_adjudication",
                "reviewerId": None,
                "labels": [],
                "labelSetComplete": None,
                "candidateEvidence": spans,
                "observedContext": observed_context,
                "authority": "review prompt only; observed roles and signature vocabulary are not labels",
            })
    task_bytes = b"".join(
        (json.dumps(task, sort_keys=True, ensure_ascii=False) + "\n").encode("utf-8")
        for task in tasks
    )
    strata = Counter((str(row.get("role", "unknown")), _uncertainty_stratum(row))
                     for row in selected)
    sampling_group_counts = Counter(_owner_group(row) for row in selected)
    manifest = {
        "schema": "info_geometry.taxonomy_adjudication_queue_manifest.v2",
        "sourceSnapshotSha256": snapshot.get("pathContentManifestSha256"),
        "sourceSnapshotConsistency": {
            "status": consistency_status,
            "inventoryScope": inventory_scope,
            "inventoryConsistentDuringScan": inventory_consistent,
            "wholeWorktreeConsistentDuringScan": whole_worktree_consistent,
            "changedPathCountDuringScan": len(changed_paths),
            "changedPathsDuringScan": sorted(changed_paths),
            "selectedSourcePaths": sorted(row["path"] for row in selected),
            "selectedSourceHashesMatchMapAtQueueTime": True,
        },
        "scannerSourceSha256": provenance.get("scannerSourceSha256"),
        "lakeManifestSha256": provenance.get("lakeManifestSha256"),
        "selectionAlgorithm": "deterministic_role_uncertainty_round_robin_v1",
        "seed": seed,
        "requestedArtifactLimit": limit,
        "maxArtifactsPerModuleOrOwner": max_per_owner,
        "candidateArtifactCount": candidate_count,
        "candidateArtifactCountAfterChangedPathExclusion": len(candidates),
        "observedUnreviewableTextCandidateCount": unreviewable_text_count,
        "sourceHashVerifiedCandidateCount": source_hash_verified_count,
        "staleOrMissingSourceCandidateCount": stale_or_missing_source_count,
        "staleOrMissingSourcePaths": sorted(stale_or_missing_source_paths),
        "selectedArtifactCount": len(selected),
        "taskCount": len(tasks),
        "selectedStrata": {
            f"{role}|{uncertainty}": count
            for (role, uncertainty), count in sorted(strata.items())
        },
        "selectedSamplingGroups": dict(sorted(sampling_group_counts.items())),
        "infotreeDnaArtifactCount": len(dna_by_path),
        "taskRowsSha256": _sha256(task_bytes),
        "signatureVocabularyReferenceOnly": [
            {"name": item["name"], "signature": item["signature"]}
            for item in ARCHETYPE_SIGNATURES
        ],
        "authority": "no taxonomy labels assigned; human adjudication required",
    }
    return tasks, manifest


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("refactoring_map", type=Path)
    parser.add_argument("--repo-root", type=Path, default=ROOT)
    parser.add_argument("--limit", type=int, default=80)
    parser.add_argument("--max-per-owner", type=int, default=3)
    parser.add_argument("--seed", default="taxonomy-review-v1")
    parser.add_argument("--infotree-dna", type=Path,
                        help="optional source-bound InfoTree DNA JSONL feature rows")
    parser.add_argument(
        "--allow-scoped-review-from-inconsistent-map",
        action="store_true",
        help=("allow a review sample from an inconsistent map only after excluding "
              "reported changed paths and checking each selected current source hash"),
    )
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument("--manifest-out", type=Path, required=True)
    args = parser.parse_args()
    tasks, manifest = build_adjudication_queue(
        _read_json(args.refactoring_map), args.repo_root,
        limit=args.limit, max_per_owner=args.max_per_owner, seed=args.seed,
        infotree_dna=_read_jsonl(args.infotree_dna) if args.infotree_dna else None,
        allow_scoped_review=args.allow_scoped_review_from_inconsistent_map,
    )
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text("".join(
        json.dumps(task, sort_keys=True, ensure_ascii=False) + "\n" for task in tasks
    ), encoding="utf-8")
    args.manifest_out.parent.mkdir(parents=True, exist_ok=True)
    args.manifest_out.write_text(json.dumps(manifest, sort_keys=True, indent=2) + "\n",
                                 encoding="utf-8")
    print(json.dumps({"artifactCount": manifest["selectedArtifactCount"],
                      "taskCount": manifest["taskCount"],
                      "rowsSha256": manifest["taskRowsSha256"],
                      "out": str(args.out)}, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
