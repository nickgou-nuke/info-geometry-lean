#!/usr/bin/env python3
"""Inventory counterexample/obstruction declarations in Lean owners.

This is deliberately lexical navigation, not a proof checker. All physical
folders are searched except Git metadata; skipped symlinks and read failures
are reported. Name/syntax matches and same-file positive-name candidates must
be reviewed against actual Lean owners and do not certify a repair.
"""

from __future__ import annotations

import argparse
import json
import re
import os
import hashlib
from pathlib import Path


DECLARATION = re.compile(
    r"\b(theorem|lemma|example)\s+(?:(«[^»]+»|[^\s:({\[=]+))?"
)
NEGATIVE_MARKERS = (
    "counterexample",
    "obstruction",
    "does_not",
    "need_not",
    "not_",
    "nonmultip",
    "not_exact",
    "not_injective",
)
POSITIVE_MARKERS = (
    "iff",
    "preserv",
    "reconstruct",
    "idempotent",
    "invariant",
    "exact",
    "recovery",
    "sum_zero",
)

# Generated dependency trees are not repository-owned Lean sources and can
# contain tens of thousands of replayed files.  They are reported as skipped
# surfaces rather than traversed; external reference submodules remain
# visible for provenance review.
SKIP_DIRECTORIES = {".git", ".lake", ".kilo", "node_modules", "__pycache__", "external_refs"}


def category(name: str) -> str:
    lowered = name.lower()
    if "counterexample" in lowered:
        return "countermodel"
    if "obstruction" in lowered or "nonmultip" in lowered:
        return "obstruction"
    if "injective" in lowered or "separate" in lowered:
        return "identifiability"
    return "negative-boundary"


def mask_comments_and_strings(source: str) -> str:
    """Mask nested comments and strings, preserving newlines and offsets."""
    result = list(source)
    i, depth, quoted = 0, 0, False
    while i < len(source):
        width = 1
        mask = depth > 0 or quoted
        if depth:
            if source.startswith("/-", i):
                depth += 1
                width = 2
            elif source.startswith("-/", i):
                depth -= 1
                width = 2
        elif quoted:
            if source[i] == "\\":
                width = min(2, len(source) - i)
            elif source[i] == '"':
                quoted = False
        elif source.startswith("/-", i):
            depth, width, mask = 1, 2, True
        elif source.startswith("--", i):
            end = source.find("\n", i)
            width = (len(source) if end < 0 else end) - i
            mask = True
        elif source[i] == '"':
            quoted, mask = True, True
        if mask:
            for j in range(i, i + width):
                if source[j] != "\n":
                    result[j] = " "
        i += width
    return "".join(result)


def surface(path: Path) -> str:
    if "external_refs" in path.parts:
        return "external-ref"
    if ".lake" in path.parts or "node_modules" in path.parts:
        return "dependency-or-build"
    if path.parts[0] in {"artifacts", "reports", "witnesses"}:
        return "generated-artifact"
    if path.parts[0] in {".runtime", ".hermes"}:
        return "runtime-state"
    if path.parts[0] in {"lean", "lib", "tests", "proofs", "tools", "scripts"}:
        return "repo-owned"
    return "other-review-required"


def inventory(root: Path) -> dict[str, object]:
    """Walk every physical folder except Git metadata; report every omission.

    Candidate detection remains lexical, not a proof or completeness claim.
    Symlinks are not followed, preventing cycles and traversal outside root.
    """
    root = root.resolve()
    rows: list[dict[str, object]] = []
    files, skipped, errors, paths = [], [], [], []
    def onerror(error: OSError) -> None:
        errors.append({"path": str(error.filename), "error": str(error)})
    for directory, dirs, names in os.walk(root, followlinks=False, onerror=onerror):
        for name in dirs.copy():
            path = Path(directory) / name
            if name in SKIP_DIRECTORIES or path.is_symlink():
                dirs.remove(name)
                reason = "git-metadata" if name == ".git" else (
                    "external-ref" if name == "external_refs" else (
                        "dependency-or-build" if name in SKIP_DIRECTORIES else "symlink"))
                skipped.append({"path": str(path.relative_to(root)), "reason": reason})
        dirs.sort()
        paths.extend(Path(directory) / name for name in names if name.endswith(".lean"))
    for path in sorted(paths):
        relative = path.relative_to(root)
        if path.is_symlink():
            skipped.append({"path": str(relative), "reason": "symlink"})
            continue
        try:
            data = path.read_bytes()
            source = data.decode("utf-8")
        except (OSError, UnicodeError) as error:
            errors.append({"path": str(relative), "error": str(error)})
            continue
        metadata = {"file": str(relative), "surface": surface(relative),
                    "sha256": hashlib.sha256(data).hexdigest()}
        files.append(metadata)
        masked = mask_comments_and_strings(source)
        declarations = [
            (source.count("\n", 0, match.start()) + 1, match.group(1),
             None if match.group(1) == "example" else match.group(2), match.end())
            for match in DECLARATION.finditer(masked)
        ]
        positive_companions = sorted(
            name for _, _, name, _ in declarations
            if name and any(marker in name.lower() for marker in POSITIVE_MARKERS)
        )
        for index, (line_number, kind, name, offset) in enumerate(declarations):
            lowered = (name or "").lower()
            end = declarations[index + 1][3] if index + 1 < len(declarations) else len(masked)
            header = masked[offset:end].split(":=", 1)[0].split("where", 1)[0]
            reasons = []
            if any(marker in lowered for marker in NEGATIVE_MARKERS):
                reasons.append("negative-name")
            if any(token in header for token in ("≠", "¬", "False")):
                reasons.append("negative-header-syntax")
            if reasons:
                rows.append(
                    {
                        **metadata,
                        "line": line_number,
                        "kind": kind,
                        "name": name,
                        "category": category(name or ""),
                        "reasons": reasons,
                        "same_file_positive_name_candidates": positive_companions,
                        "repair_status": "requires-owner-and-dependent-review",
                    }
                )
    return {"schema_version": 2, "files": files, "candidates": rows,
            "skipped": skipped, "errors": errors,
            "authority": "lexical navigation only; no semantic completeness or repair certification",
            "limitations": ["not a Lean parser", "negative hypotheses can be false positives",
                            "indirect counterexamples may be missed", "symlinks not followed",
                            "binder defaults can truncate lexical headers"]}


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--root", type=Path, default=Path.cwd())
    parser.add_argument("--json", action="store_true")
    args = parser.parse_args()
    report = inventory(args.root.resolve())
    rows = report["candidates"]
    if args.json:
        print(json.dumps(report, indent=2, sort_keys=True, ensure_ascii=False))
        if report["errors"]:
            raise SystemExit(1)
        return
    print(f"counterexample-style declarations: {len(rows)}")
    print(report["authority"])
    print(f"Lean files scanned: {len(report['files'])}")
    print(f"skipped paths: {len(report['skipped'])}; read errors: {len(report['errors'])}")
    by_category: dict[str, int] = {}
    for row in rows:
        key = str(row["category"])
        by_category[key] = by_category.get(key, 0) + 1
    for key in sorted(by_category):
        print(f"{key}: {by_category[key]}")
    for row in rows:
        print(f"{row['file']}:{row['line']}: {row['kind']} {row['name']} [{row['surface']}; {row['category']}]")
    if report["errors"]:
        raise SystemExit(1)


if __name__ == "__main__":
    try:
        main()
    except BrokenPipeError:
        pass
