#!/usr/bin/env python3
"""Streaming weak labels for commit-level code-change categories.

Categories are multi-label change archetypes, not Linnaean ranks. The rules
are navigation/classification evidence and do not assert semantic equivalence.
Input is the commit JSONL emitted by ``evolution_extract.py``.
"""
from __future__ import annotations

import argparse
import json
import re
import sqlite3
import sys
import tempfile
from pathlib import Path
from typing import Iterable, Iterator, TextIO

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


def classify(subject: str, body: str,
             paths: Iterable[str] | None = None) -> list[dict]:
    """Return all matching change categories, with explicit rule provenance."""
    text = f"{subject}\n{body}"
    labels = [
        {"species": name, "confidence": score, "matched": [name]}
        for name, pattern, score in RULES if pattern.search(text)
    ]
    by_species = {row["species"]: row for row in labels}
    seen_path_evidence: set[str] = set()
    for path in paths or ():
        for pattern, species in PATH_HINTS:
            if pattern.search(path):
                evidence = f"path-hint:{species}"
                if evidence in seen_path_evidence:
                    continue
                seen_path_evidence.add(evidence)
                if species in by_species:
                    by_species[species]["matched"].append(evidence)
                else:
                    by_species[species] = {
                        "species": species, "confidence": .5,
                        "matched": [evidence],
                    }
    if not by_species:
        return [{"species": "Feature Introduction", "confidence": .4,
                 "matched": ["default:no-rule-match"]}]
    return list(by_species.values())


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
        yield {"sha": commit["sha"], "labels": labels, "method": "weak-rule-v2"}


def iter_jsonl(source: TextIO) -> Iterator[dict]:
    for line_number, line in enumerate(source, 1):
        if line.strip():
            try:
                yield json.loads(line)
            except json.JSONDecodeError as exc:
                raise ValueError(f"invalid JSONL at line {line_number}: {exc}") from exc


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("input", type=Path, nargs="?", help="commit JSONL; stdin when omitted")
    parser.add_argument("--out", type=Path, help="label JSONL; stdout when omitted")
    parser.add_argument("--paths", type=Path, help="optional commit-file JSONL from evolution_extract.py")
    args = parser.parse_args()
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
