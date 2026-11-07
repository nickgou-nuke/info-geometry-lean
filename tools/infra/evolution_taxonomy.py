#!/usr/bin/env python3
"""Streaming weak labels for commit-level code-change categories.

Categories are non-hierarchical, multi-label change facets, not species or
Linnaean ranks. Rule weights are not calibrated probabilities. Input is the
commit JSONL emitted by ``evolution_extract.py``.
"""
from __future__ import annotations

import argparse
import json
import re
import sqlite3
import sys
import tempfile
from pathlib import Path
from typing import Any, Iterable, Iterator, Mapping, TextIO

RULES: list[tuple[str, re.Pattern[str], float]] = [
    ("Revert/Backout", re.compile(r"^revert\b", re.I), 1.0),
    ("Security Hardening", re.compile(r"\b(security|vulnerab|cve|exploit|harden|sanitiz|injection)\w*\b", re.I), .9),
    ("Bug Fix", re.compile(r"\b(fix|bug|regression|patch|correct|fixup)\w*\b", re.I), .85),
    ("Test Evolution", re.compile(r"\b(test|tests|testing|flaky|harness|assert|spec)\b|t/\d{4}|^t[0-9]{4}", re.I), .8),
    ("Documentation/Developer UX", re.compile(r"\b(doc|docs|documentation|manpage|readme|changelog|comment)\b", re.I), .8),
    ("Refactor/Restructure", re.compile(r"\b(refactor|cleanup|clean-up|rename|restructur|reorganiz)\w*\b", re.I), .8),
    ("Performance Optimization", re.compile(r"\b(perf|performance|optimiz[ae]|faster|speedup|hotspot|bottleneck)\w*\b", re.I), .8),
    ("Build/Tooling/CI", re.compile(r"\b(build|makefile|cmake|ci|workflow|lint|format|tooling|pipeline)\b", re.I), .75),
    ("Dependency/Vendor/Third-party sync", re.compile(r"\b(depend|vendor|submodule|subtree|package|pip|cargo|npm|maven)\w*\b", re.I), .75),
    ("Release/Versioning/Meta", re.compile(r"^merge\b|\b(release|version|bump|tag|milestone)\b", re.I), .7),
    ("Localization/Portability", re.compile(r"\b(localization|l10n|international|i18n|portability|windows|macos|linux|platform)\b", re.I), .7),
]
PATH_HINTS: list[tuple[re.Pattern[str], str]] = [
    (re.compile(r"^t/|test_|_test\."), "Test Evolution"),
    (re.compile(r"^Documentation/|^docs/|^man/|\.md$|\.rst$"), "Documentation/Developer UX"),
    (re.compile(r"^Makefile|^CMakeLists|\.github/|^ci/|^script/|\.ya?ml$"), "Build/Tooling/CI"),
    (re.compile(r"^vendor/|^third_party/|^deps/|\.lock$|go\.mod|Cargo\.toml|package\.json"), "Dependency/Vendor/Third-party sync"),
]

SCHEMA_VERSION = "info_geometry.commit_change_labels.v1"
METHOD_VERSION = "weak-rule-v3"
EVIDENCE_KINDS: tuple[str, ...] = (
    "subjectBodyRule",
    "pathHint",
    "defaultNoRuleMatch",
    "other",
)

CATEGORY_IDS = {
    "Revert/Backout": "revertBackout",
    "Security Hardening": "securityHardening",
    "Bug Fix": "bugFix",
    "Test Evolution": "testEvolution",
    "Documentation/Developer UX": "documentationDeveloperUx",
    "Refactor/Restructure": "refactorRestructure",
    "Performance Optimization": "performanceOptimization",
    "Build/Tooling/CI": "buildToolingCi",
    "Dependency/Vendor/Third-party sync": "dependencyVendorSync",
    "Release/Versioning/Meta": "releaseVersioningMeta",
    "Localization/Portability": "localizationPortability",
    "Feature Introduction": "featureIntroduction",
}

GEM_CLADE_IDS: dict[str, str] = {
    "Gravito-Electric Monopole": "GCladeI_GravitoElectricMonopole",
    "Gravito-Magnetic Dipole": "GCladeII_GravitoMagneticDipole",
    "Lense-Thirring Coriolis": "GCladeIII_LenseThirringCoriolis",
    "Work-Free Coriolis": "GCladeIV_WorkFreeCoriolis",
    "Second-Order Centrifugal": "GCladeV_SecondOrderCentrifugal",
    "Kerr Ergosphere": "GCladeVI_KerrErgosphere",
    "Einstein-Cartan Torsion": "GCladeVII_EinsteinCartanTorsion",
    "Onsager Reciprocity": "GCladeVIII_OnsagerReciprocity",
    "Chiral Splitting": "GCladeIX_ChiralSplitting",
    "Mach Principle": "GCladeX_MachPrinciple",
}

GEM_EPOCH_IDS: dict[str, str] = {
    "Newtonian Gravito-Electric": "GEpoch1_NewtonianGravitoElectric",
    "Mach Relational Inertia": "GEpoch2_MachRelationalInertia",
    "Lense-Thirring 1918": "GEpoch3_LenseThirring1918",
    "Gravito-Electromagnetic Split": "GEpoch4_GravitoElectromagneticSplit",
    "Weyl Spinor Chiral Split": "GEpoch5_WeylSpinorChiralSplit",
    "Commutator Algebra": "GEpoch6_CommutatorAlgebra",
    "Second-Order Centrifugal": "GEpoch7_SecondOrderCentrifugal",
    "Kerr Ergosphere Collapse": "GEpoch8_KerrErgosphereCollapse",
}


def _evidence_kinds(evidence: Iterable[str]) -> list[str]:
    return sorted({
        "subjectBodyRule" if item.startswith("subject-body-rule:") else
        "pathHint" if item.startswith("path-hint:") else
        "defaultNoRuleMatch" if item == "default:no-rule-match" else
        "other"
        for item in evidence
    })


def _label(category: str, weight: float, evidence: list[str]) -> dict[str, Any]:
    return {
        "category": category,
        "categoryId": CATEGORY_IDS[category],
        "ruleWeightPercent": int(round(weight * 100)),
        "evidence": evidence,
        "evidenceKinds": _evidence_kinds(evidence),
        "status": "weak_rule",
    }


def classify(subject: str, body: str,
             paths: Iterable[str] | None = None) -> list[dict[str, Any]]:
    """Return all matching change categories, with explicit rule provenance."""
    text = f"{subject}\n{body}"
    labels = [
        _label(name, score, [f"subject-body-rule:{name}"])
        for name, pattern, score in RULES if pattern.search(text)
    ]
    by_category = {row["category"]: row for row in labels}
    seen_path_evidence: set[str] = set()
    for path in paths or ():
        for pattern, category in PATH_HINTS:
            if pattern.search(path):
                evidence = f"path-hint:{category}"
                if evidence in seen_path_evidence:
                    continue
                seen_path_evidence.add(evidence)
                if category in by_category:
                    by_category[category]["evidence"].append(evidence)
                    by_category[category]["evidenceKinds"] = _evidence_kinds(
                        by_category[category]["evidence"]
                    )
                else:
                    by_category[category] = _label(category, .5, [evidence])
    if not by_category:
        return [_label("Feature Introduction", .4, ["default:no-rule-match"])]
    return list(by_category.values())


def validate_label_record(record: Mapping[str, Any] | dict[str, Any]) -> None:
    """Validate one emitted commit-label JSONL record against SCHEMA_VERSION."""
    if not isinstance(record, dict):
        raise ValueError("taxonomy label record must be a JSON object")
    if record.get("schema") != SCHEMA_VERSION:
        raise ValueError(f"expected schema {SCHEMA_VERSION!r}, got {record.get('schema')!r}")
    if record.get("method") != METHOD_VERSION:
        raise ValueError(f"expected method {METHOD_VERSION!r}, got {record.get('method')!r}")
    sha = record.get("sha")
    if not isinstance(sha, str) or not sha.strip():
        raise ValueError("record sha must be a non-empty string")
    labels = record.get("labels")
    if not isinstance(labels, list) or not labels:
        raise ValueError("record labels must be a non-empty list")
    seen_categories: set[str] = set()
    for label in labels:
        if not isinstance(label, dict):
            raise ValueError("each label entry must be a JSON object")
        category = label.get("category")
        if not isinstance(category, str) or category not in CATEGORY_IDS:
            raise ValueError(f"unknown or invalid category: {category!r}")
        if category in seen_categories:
            raise ValueError(f"duplicate category in commit label record: {category!r}")
        seen_categories.add(category)
        expected_id = CATEGORY_IDS[category]
        if label.get("categoryId") != expected_id:
            raise ValueError(
                f"categoryId mismatch for {category!r}: expected {expected_id!r}, got {label.get('categoryId')!r}"
            )
        weight = label.get("ruleWeightPercent")
        if isinstance(weight, bool) or not isinstance(weight, int) or not (0 <= weight <= 100):
            raise ValueError(f"ruleWeightPercent must be an integer in [0, 100], got {weight!r}")
        if label.get("status") != "weak_rule":
            raise ValueError(f"label status must be 'weak_rule', got {label.get('status')!r}")
        evidence = label.get("evidence")
        if (not isinstance(evidence, list) or not evidence
                or any(not isinstance(item, str) or not item.strip() for item in evidence)):
            raise ValueError("label evidence must be a non-empty list of non-empty strings")
        evidence_kinds = label.get("evidenceKinds")
        if (not isinstance(evidence_kinds, list) or not evidence_kinds
                or any(kind not in EVIDENCE_KINDS for kind in evidence_kinds)):
            raise ValueError(f"invalid evidenceKinds: {evidence_kinds!r}")
        expected_kinds = _evidence_kinds(evidence)
        if evidence_kinds != expected_kinds:
            raise ValueError(
                f"evidenceKinds {evidence_kinds!r} does not match derived kinds {expected_kinds!r}"
            )


def iter_labels(records: Iterable[dict], path_index: sqlite3.Connection | None = None) -> Iterator[dict]:
    """Yield labels immediately; never retain the commit history in memory."""
    for commit in records:
        if commit.get("type") != "commit":
            continue
        paths: Iterable[str] = iter(commit.get("paths", []))
        if path_index is not None:
            paths = (row[0] for row in path_index.execute(
                "SELECT path FROM commit_paths WHERE sha = ?", (commit["sha"],)
            ))
        labels = classify(commit.get("subject", ""), commit.get("body", ""), paths)
        record = {
            "schema": SCHEMA_VERSION,
            "sha": commit["sha"],
            "labels": labels,
            "method": METHOD_VERSION,
        }
        validate_label_record(record)
        yield record


def iter_jsonl(source: TextIO) -> Iterator[dict]:
    for line_number, line in enumerate(source, 1):
        if line.strip():
            try:
                yield json.loads(line)
            except json.JSONDecodeError as exc:
                raise ValueError(f"invalid JSONL at line {line_number}: {exc}") from exc


def validate_jsonl_file(path: Path) -> int:
    count = 0
    with path.open(encoding="utf-8") as stream:
        for line_number, record in enumerate(iter_jsonl(stream), 1):
            try:
                validate_label_record(record)
            except ValueError as exc:
                raise ValueError(f"{path}:{line_number}: {exc}") from exc
            count += 1
    return count


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("input", type=Path, nargs="?", help="commit JSONL; stdin when omitted")
    parser.add_argument("--out", type=Path, help="label JSONL; stdout when omitted")
    parser.add_argument("--paths", type=Path, help="optional commit-file JSONL from evolution_extract.py")
    parser.add_argument("--validate-jsonl", type=Path,
                        help="validate an existing commit_change_labels.v1 JSONL file and exit")
    args = parser.parse_args()
    if args.validate_jsonl is not None:
        try:
            validated = validate_jsonl_file(args.validate_jsonl)
        except (OSError, ValueError) as exc:
            print(f"[evolution_taxonomy] validation failed: {exc}", file=sys.stderr, flush=True)
            return 2
        print(f"[evolution_taxonomy] validated {validated} label records in {args.validate_jsonl}",
              file=sys.stderr, flush=True)
        return 0
    source = args.input.open(encoding="utf-8") if args.input else sys.stdin
    output = args.out.open("w", encoding="utf-8") if args.out else sys.stdout
    count = 0
    temp_dir = tempfile.TemporaryDirectory(prefix="evolution-taxonomy-") if args.paths else None
    path_index = sqlite3.connect(Path(temp_dir.name) / "paths.sqlite3") if temp_dir else None
    try:
        if path_index is not None:
            path_index.execute("CREATE TABLE commit_paths (sha TEXT NOT NULL, path TEXT NOT NULL)")
            with args.paths.open(encoding="utf-8") as path_stream:
                batch = []
                for row in iter_jsonl(path_stream):
                    for path in (row.get("old_path"), row.get("path")):
                        if path is not None:
                            batch.append((row["sha"], path))
                    if len(batch) >= 2048:
                        path_index.executemany("INSERT INTO commit_paths VALUES (?, ?)", batch)
                        path_index.commit()
                        batch.clear()
                if batch:
                    path_index.executemany("INSERT INTO commit_paths VALUES (?, ?)", batch)
                    path_index.commit()
            path_index.execute("CREATE INDEX commit_paths_sha ON commit_paths(sha)")
        for label in iter_labels(iter_jsonl(source), path_index):
            output.write(json.dumps(label, ensure_ascii=False) + "\n")
            count += 1
        if args.out:
            output.flush()
        print(f"[evolution_taxonomy] streamed labels for {count} commits",
              file=sys.stderr, flush=True)
    finally:
        if args.input:
            source.close()
        if args.out:
            output.close()
        if path_index is not None:
            path_index.close()
        if temp_dir is not None:
            temp_dir.cleanup()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
