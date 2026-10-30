#!/usr/bin/env python3
"""Build a source-bound, group-split corpus from adjudicated taxonomy labels.

The builder materializes only annotated current files. Commit histories and
weak-rule predictions are not training examples or labels.
"""
from __future__ import annotations

import argparse
import gzip
import hashlib
import json
from collections import Counter, defaultdict
from pathlib import Path
from typing import Any, Iterable


MAP_SCHEMA = "info_geometry.refactoring_map.v1"
ANNOTATION_SCHEMA = "info_geometry.reviewed_taxonomy_annotation.v4"
CORPUS_SCHEMA = "info_geometry.reviewed_taxonomy_corpus.v4"
CORPUS_MANIFEST_SCHEMA = "info_geometry.reviewed_taxonomy_corpus_manifest.v4"
LABEL_CODEBOOK_SCHEMA = "info_geometry.taxonomy_label_codebook.v1"
LOCAL_EDGE_KINDS = {
    "lean_source_import", "python_import", "test_import",
    "lean_source_import_outside_inventory",
}


def _read_json(path: Path) -> dict[str, Any]:
    opener = gzip.open if path.suffix == ".gz" else open
    with opener(path, "rt", encoding="utf-8") as stream:
        value = json.load(stream)
    if not isinstance(value, dict):
        raise ValueError(f"{path}: expected a JSON object")
    return value


def _sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def _is_sha256(value: Any) -> bool:
    if not isinstance(value, str) or len(value) != 64:
        return False
    try:
        int(value, 16)
    except ValueError:
        return False
    return True


def _split_group(record: dict[str, Any]) -> str:
    module = record.get("module")
    if isinstance(module, str) and module:
        return f"module:{module}"
    module_candidate = record.get("moduleCandidate")
    source_root = record.get("moduleCandidateSourceRoot")
    if (isinstance(module_candidate, str) and module_candidate
            and isinstance(source_root, str) and source_root):
        return f"module_candidate:{source_root}:{module_candidate}"
    owner = record.get("owner")
    owner_status = str(record.get("ownerStatus", ""))
    owner_is_uncertain = (owner_status.startswith(("uncertain", "unresolved"))
                          or (isinstance(owner, str) and owner.startswith("unresolved_")))
    if (isinstance(owner, str) and owner and owner != "unresolved"
            and not owner_is_uncertain):
        return f"owner:{owner}"
    path = str(record["path"])
    return f"directory:{Path(path).parent.as_posix()}"


def _iterative_group_splits(group_labels: dict[str, Counter[str]],
                            group_sizes: dict[str, int], *, seed: str) -> dict[str, str]:
    """Assign indivisible groups while approximately stratifying facet labels.

    This adapts iterative multi-label stratification to the pipeline's module,
    owner, and exact-content holdout components. Labels are counted by artifact;
    groups stay intact, so label balance never overrides leakage isolation.
    """
    if set(group_labels) != set(group_sizes):
        raise ValueError("group label counts and sizes must have identical keys")
    if any(size < 1 for size in group_sizes.values()):
        raise ValueError("every holdout group must contain at least one artifact")
    splits = ("train", "validation", "test")
    ratios = {"train": 0.8, "validation": 0.1, "test": 0.1}
    total_size = sum(group_sizes.values())
    total_labels: Counter[str] = Counter()
    label_group_support: Counter[str] = Counter()
    for counts in group_labels.values():
        total_labels.update(counts)
        label_group_support.update(label for label, count in counts.items() if count > 0)
    label_targets = {}
    for label, count in total_labels.items():
        minimum = 1.0 if label_group_support[label] >= len(splits) else 0.0
        residual = max(0.0, count - minimum * len(splits))
        label_targets[label] = {
            split: minimum + residual * ratios[split] for split in splits
        }
    size_targets = {split: total_size * ratios[split] for split in splits}
    assigned_labels = {split: Counter() for split in splits}
    assigned_sizes = Counter()
    remaining = set(group_labels)
    assignments: dict[str, str] = {}

    def tie_key(value: str) -> str:
        return hashlib.sha256(f"{seed}\0{value}".encode("utf-8")).hexdigest()

    while remaining:
        remaining_support: Counter[str] = Counter()
        for group in remaining:
            remaining_support.update(label for label, count in group_labels[group].items()
                                     if count > 0)
        active_labels = [label for label, support in remaining_support.items() if support]
        rarest_label = None
        if active_labels:
            rarest_label = min(active_labels, key=lambda label: (
                remaining_support[label], tie_key("label:" + label), label
            ))
            candidates = [group for group in remaining
                          if group_labels[group].get(rarest_label, 0) > 0]
            group = min(candidates, key=lambda item: (
                -group_labels[item][rarest_label], tie_key("group:" + item), item
            ))
        else:
            group = min(remaining, key=lambda item: (tie_key("group:" + item), item))

        def gain(split: str) -> float:
            value = 0.0
            if rarest_label is not None:
                count = group_labels[group][rarest_label]
                label = rarest_label
                target = label_targets.get(label, {}).get(split, 0.0)
                deficit = target - assigned_labels[split][label]
                value += (deficit * deficit - (deficit - count) ** 2) / max(total_labels[label], 1)
            size_deficit = size_targets[split] - assigned_sizes[split]
            value += 0.02 * (
                size_deficit * size_deficit
                - (size_deficit - group_sizes[group]) ** 2
            ) / max(total_size, 1)
            return value

        selected_split = max(splits, key=lambda split: (
            gain(split), size_targets[split] - assigned_sizes[split],
            tie_key(f"split:{group}:{split}"),
        ))
        assignments[group] = selected_split
        assigned_sizes[selected_split] += group_sizes[group]
        assigned_labels[selected_split].update(group_labels[group])
        remaining.remove(group)
    return assignments


def _holdout_groups(artifacts: set[str], files: dict[str, dict[str, Any]]) -> dict[str, str]:
    """Keep module/owner peers and exact-content aliases in the same split."""
    parent = {artifact: artifact for artifact in artifacts}

    def find(artifact: str) -> str:
        while parent[artifact] != artifact:
            parent[artifact] = parent[parent[artifact]]
            artifact = parent[artifact]
        return artifact

    def union(left: str, right: str) -> None:
        root_left, root_right = find(left), find(right)
        if root_left != root_right:
            first, second = sorted((root_left, root_right))
            parent[second] = first

    first_by_group: dict[str, str] = {}
    first_by_content: dict[str, str] = {}
    for artifact in sorted(artifacts):
        record = files[artifact]
        keys = [f"layout:{_split_group(record)}"]
        content_hash = record.get("contentSha256")
        if isinstance(content_hash, str) and content_hash:
            keys.append(f"content:{content_hash}")
        for key in keys:
            previous = first_by_group.setdefault(key, artifact)
            union(artifact, previous)
    members_by_root: dict[str, list[str]] = defaultdict(list)
    for artifact in artifacts:
        members_by_root[find(artifact)].append(artifact)
    group_ids = {}
    for members in members_by_root.values():
        identity = "\0".join(sorted(members))
        group_id = "holdout:" + hashlib.sha256(identity.encode("utf-8")).hexdigest()
        for artifact in members:
            group_ids[artifact] = group_id
    return group_ids


def _validate_annotation(annotation: dict[str, Any], files: dict[str, dict[str, Any]],
                         snapshot_hash: str) -> tuple[
                             str, str, list[str], dict[str, str],
                             list[dict[str, Any]], dict[str, Any]
                         ]:
    if annotation.get("schema") != ANNOTATION_SCHEMA:
        raise ValueError("unsupported reviewed-taxonomy annotation schema")
    if annotation.get("reviewStatus") != "human_adjudicated":
        raise ValueError("training labels must have reviewStatus=human_adjudicated")
    reviewer = annotation.get("reviewerId")
    if not isinstance(reviewer, str) or not reviewer.strip():
        raise ValueError("consensus labels require a reviewerId")
    reviewer_ids = annotation.get("reviewerIds")
    if (reviewer != reviewer.strip()
            or not isinstance(reviewer_ids, list) or len(reviewer_ids) < 2
            or any(not isinstance(value, str) or not value.strip() or value != value.strip()
                   for value in reviewer_ids)
            or len(reviewer_ids) != len(set(reviewer_ids))
            or reviewer_ids != sorted(reviewer_ids)
            or reviewer.strip() not in reviewer_ids):
        raise ValueError("training labels require at least two distinct consensus reviewerIds")
    reviewer_count = annotation.get("independentReviewerCount")
    if (isinstance(reviewer_count, bool) or not isinstance(reviewer_count, int)
            or reviewer_count != len(reviewer_ids)
            or annotation.get("consensusMethod") != "unanimous_exact_label_set"):
        raise ValueError("training labels require a matching unanimous reviewer consensus receipt")
    artifact = annotation.get("artifactId")
    if not isinstance(artifact, str) or artifact not in files:
        raise ValueError("annotation references an artifact absent from the source map")
    if annotation.get("sourceSnapshotSha256") != snapshot_hash:
        raise ValueError(f"annotation snapshot differs from the source map for {artifact}")
    if annotation.get("sourceSha256") != files[artifact].get("contentSha256"):
        raise ValueError(f"annotation source hash differs from the source map for {artifact}")
    facet = annotation.get("facet")
    if facet not in {"artifact_role", "semantic_archetype"}:
        raise ValueError("facet must be artifact_role or semantic_archetype")
    labels = annotation.get("labels")
    if (not isinstance(labels, list)
            or any(not isinstance(label, str) or not label.strip()
                   or label != label.strip() for label in labels)
            or len(labels) != len(set(labels))):
        raise ValueError("labels must be a complete list of unique non-empty strings; it may be empty")
    definitions = annotation.get("labelDefinitions")
    if (not isinstance(definitions, dict) or set(definitions) != set(labels)
            or any(not isinstance(value, str) or len(value.split()) < 2
                   or value != " ".join(value.split())
                   for value in definitions.values())):
        raise ValueError("annotation requires one normalized definition per selected label")
    if annotation.get("labelSetComplete") is not True:
        raise ValueError("multi-label training requires labelSetComplete=true per facet")
    evidence = annotation.get("evidence")
    if not isinstance(evidence, list) or not evidence:
        raise ValueError("human-adjudicated labels require evidence references")
    for witness in evidence:
        if not isinstance(witness, dict) or witness.get("kind") != "source_span":
            raise ValueError("each label must cite a source_span witness")
        start, end = witness.get("startLine"), witness.get("endLine")
        if (isinstance(start, bool) or isinstance(end, bool)
                or not isinstance(start, int) or not isinstance(end, int)
                or start < 1 or end < start):
            raise ValueError(f"invalid source span for {artifact}")
        if witness.get("sourceSha256") != annotation.get("sourceSha256"):
            raise ValueError(f"source-span witness hash differs for {artifact}")
    evidence_reviewers = {witness.get("reviewerId") for witness in evidence}
    if not set(reviewer_ids) <= evidence_reviewers:
        raise ValueError(f"consensus source-span evidence is missing a reviewer for {artifact}")
    annotation_id = annotation.get("annotationId")
    if not isinstance(annotation_id, str) or not annotation_id.strip():
        raise ValueError("annotation requires a stable annotationId")
    consensus = {
        "reviewerIds": reviewer_ids,
        "independentReviewerCount": reviewer_count,
        "method": annotation["consensusMethod"],
    }
    return artifact, facet, list(labels), dict(definitions), evidence, consensus


def build_reviewed_corpus(refactoring_map: dict[str, Any],
                          annotations: Iterable[dict[str, Any]],
                          repo_root: Path, *, split_seed: str = "taxonomy-v1") -> dict[str, Any]:
    """Validate adjudicated labels and emit one current-source row per artifact."""
    if refactoring_map.get("schema") != MAP_SCHEMA:
        raise ValueError(f"expected {MAP_SCHEMA}")
    snapshot = refactoring_map.get("sourceSnapshot") or {}
    analysis = refactoring_map.get("analysisProvenance") or {}
    if snapshot.get("worktreeConsistentDuringScan") is not True:
        raise ValueError("refusing an inconsistent worktree source map")
    if analysis.get("analysisInputsConsistentDuringScan") is not True:
        raise ValueError("refusing source map with missing or unstable scanner/Lake inputs")
    snapshot_hash = snapshot.get("pathContentManifestSha256")
    scanner_hash = analysis.get("scannerSourceSha256")
    lake_hash = analysis.get("lakeManifestSha256")
    if not all(_is_sha256(value) for value in (snapshot_hash, scanner_hash, lake_hash)):
        raise ValueError("source map lacks complete SHA-256 analysis provenance")
    file_rows = [row for row in refactoring_map.get("files", [])
                 if isinstance(row, dict) and isinstance(row.get("path"), str)]
    files = {row["path"]: row for row in file_rows}
    if len(files) != len(file_rows):
        raise ValueError("source map contains duplicate artifact paths")
    by_artifact: dict[str, dict[str, Any]] = {}
    annotation_ids: set[str] = set()
    artifact_facets: set[tuple[str, str]] = set()
    codebook: dict[tuple[str, str], str] = {}
    for annotation in annotations:
        artifact, facet, labels, definitions, evidence, consensus = _validate_annotation(
            annotation, files, snapshot_hash
        )
        for label, definition in definitions.items():
            key = (facet, label)
            previous = codebook.setdefault(key, definition)
            if previous != definition:
                raise ValueError(f"conflicting definitions for {facet} label {label!r}")
        annotation_id = annotation["annotationId"]
        if annotation_id in annotation_ids:
            raise ValueError(f"duplicate annotationId: {annotation_id}")
        annotation_ids.add(annotation_id)
        artifact_facet = (artifact, facet)
        if artifact_facet in artifact_facets:
            raise ValueError(f"multiple adjudications for {artifact} facet {facet}")
        artifact_facets.add(artifact_facet)
        bucket = by_artifact.setdefault(artifact, {
            "labels": {}, "labelDefinitions": {}, "evidence": {},
            "consensusByFacet": {}, "annotationIds": []
        })
        bucket["labels"][facet] = sorted(labels)
        bucket["labelDefinitions"][facet] = definitions
        bucket["evidence"][facet] = evidence
        bucket["consensusByFacet"][facet] = consensus
        bucket.setdefault("labelSetCompleteByFacet", {})[facet] = True
        bucket["annotationIds"].append(annotation_id)

    typed_context: dict[str, Counter[str]] = defaultdict(Counter)
    for edge in refactoring_map.get("dependencyEdges", []):
        if not isinstance(edge, dict) or edge.get("kind") not in LOCAL_EDGE_KINDS:
            continue
        source, target, kind = edge.get("from"), edge.get("to"), edge["kind"]
        if source in files:
            typed_context[source][f"outgoing:{kind}"] += 1
        if target in files:
            typed_context[target][f"incoming:{kind}"] += 1
    declaration_kinds: dict[str, Counter[str]] = defaultdict(Counter)
    for declaration in refactoring_map.get("leanDeclarationCandidates", []):
        if isinstance(declaration, dict) and declaration.get("sourcePath") in files:
            declaration_kinds[declaration["sourcePath"]][str(declaration.get("kind", "unknown"))] += 1

    holdout_groups = _holdout_groups(set(by_artifact), files)
    group_labels: dict[str, Counter[str]] = defaultdict(Counter)
    group_sizes: Counter[str] = Counter()
    for artifact, payload in by_artifact.items():
        group = holdout_groups[artifact]
        group_sizes[group] += 1
        for facet, labels in payload["labels"].items():
            group_labels[group].update({f"{facet}={label}": 1 for label in labels})
    group_splits = _iterative_group_splits(
        dict(group_labels), dict(group_sizes), seed=split_seed
    )
    split_label_counts: dict[str, Counter[str]] = {
        split: Counter() for split in ("train", "validation", "test")
    }
    rows = []
    for artifact, payload in sorted(by_artifact.items()):
        record = files[artifact]
        source_path = repo_root / artifact
        if not source_path.is_file() or _sha256_file(source_path) != record.get("contentSha256"):
            raise ValueError(f"current source changed or is unavailable for {artifact}")
        source_text = source_path.read_text(encoding="utf-8")
        line_count = len(source_text.splitlines())
        for facet_evidence in payload["evidence"].values():
            if any(witness["endLine"] > line_count for witness in facet_evidence):
                raise ValueError(f"source-span witness exceeds current file length for {artifact}")
        group = holdout_groups[artifact]
        split = group_splits[group]
        for facet, labels in payload["labels"].items():
            split_label_counts[split].update({f"{facet}={label}": 1 for label in labels})
        rows.append({
            "schema": CORPUS_SCHEMA,
            "artifactId": artifact,
            "sourceSha256": record["contentSha256"],
            "splitGroup": group,
            "split": split,
            "modelInput": {
                "sourceText": source_text,
                "typedNeighborhoodCounts": dict(sorted(typed_context[artifact].items())),
                "declarationKindCounts": dict(sorted(declaration_kinds[artifact].items())),
            },
            "labels": payload["labels"],
            "labelDefinitionsByFacet": payload["labelDefinitions"],
            "labelSetCompleteByFacet": payload["labelSetCompleteByFacet"],
            "consensusByFacet": payload["consensusByFacet"],
            "evidenceByFacet": payload["evidence"],
            "annotationIds": sorted(payload["annotationIds"]),
            "provenance": {
                "sourceSnapshotSha256": snapshot_hash,
                "scannerSourceSha256": scanner_hash,
                "lakeManifestSha256": lake_hash,
                "labelAuthority": "human_adjudicated",
            },
        })
    split_counts = Counter(row["split"] for row in rows)
    row_bytes = b"".join((json.dumps(row, sort_keys=True, ensure_ascii=False) + "\n").encode()
                         for row in rows)
    codebook_rows = [
        {"facet": facet, "label": label, "definition": definition}
        for (facet, label), definition in sorted(codebook.items())
    ]
    codebook_payload = {"schema": LABEL_CODEBOOK_SCHEMA, "labels": codebook_rows}
    codebook_sha256 = hashlib.sha256(json.dumps(
        codebook_payload, sort_keys=True, ensure_ascii=False, separators=(",", ":")
    ).encode("utf-8")).hexdigest()
    return {
        "schema": CORPUS_MANIFEST_SCHEMA,
        "corpusSchema": CORPUS_SCHEMA,
        "sourceSnapshotSha256": snapshot_hash,
        "scannerSourceSha256": scanner_hash,
        "lakeManifestSha256": lake_hash,
        "labelCodebookSchema": LABEL_CODEBOOK_SCHEMA,
        "labelCodebookSha256": codebook_sha256,
        "labelCodebook": codebook_rows,
        "splitStrategy": "iterative_multilabel_module_owner_content_group_holdout_v3",
        "splitSeed": split_seed,
        "groupSplits": dict(sorted(group_splits.items())),
        "splitLabelCounts": {
            split: dict(sorted(split_label_counts[split].items()))
            for split in ("train", "validation", "test")
        },
        "artifactCount": len(rows),
        "annotationCount": len(annotation_ids),
        "splitCounts": {key: split_counts.get(key, 0) for key in ("train", "validation", "test")},
        "allThreeSplitsPresent": all(split_counts.get(key, 0) > 0
                                      for key in ("train", "validation", "test")),
        "corpusRowsSha256": hashlib.sha256(row_bytes).hexdigest(),
        "rows": rows,
        "authority": "training candidates from current source plus human-adjudicated labels; no weak labels promoted",
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("refactoring_map", type=Path)
    parser.add_argument("annotations", type=Path, help="adjudicated annotation JSONL")
    parser.add_argument("--repo-root", type=Path, default=Path(__file__).resolve().parents[2])
    parser.add_argument("--split-seed", default="taxonomy-v1")
    parser.add_argument("--out", type=Path, required=True, help="corpus JSONL output")
    parser.add_argument("--manifest-out", type=Path, required=True)
    args = parser.parse_args()
    map_report = _read_json(args.refactoring_map)
    annotations = []
    with args.annotations.open("r", encoding="utf-8") as stream:
        for line_number, line in enumerate(stream, 1):
            if not line.strip():
                continue
            try:
                row = json.loads(line)
            except json.JSONDecodeError as exc:
                raise ValueError(f"{args.annotations}:{line_number}: invalid JSON") from exc
            if not isinstance(row, dict):
                raise ValueError(f"{args.annotations}:{line_number}: expected an object")
            annotations.append(row)
    result = build_reviewed_corpus(map_report, annotations, args.repo_root,
                                   split_seed=args.split_seed)
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text("".join(json.dumps(row, sort_keys=True, ensure_ascii=False) + "\n"
                                         for row in result["rows"]), encoding="utf-8")
    manifest = {key: value for key, value in result.items() if key != "rows"}
    args.manifest_out.parent.mkdir(parents=True, exist_ok=True)
    args.manifest_out.write_text(json.dumps(manifest, sort_keys=True, indent=2) + "\n",
                                 encoding="utf-8")
    print(json.dumps({"artifactCount": result["artifactCount"],
                      "splitCounts": result["splitCounts"],
                      "allThreeSplitsPresent": result["allThreeSplitsPresent"],
                      "out": str(args.out), "manifest": str(args.manifest_out)},
                     sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
