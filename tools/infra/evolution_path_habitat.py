#!/usr/bin/env python3
"""Stream extracted Git path JSONL into subsystem habitat counts.

Consumes ``evolution_extract.py --paths-output`` records. Invalid UTF-8 paths
are preserved by their extractor-provided Base64 field and grouped using the
same raw bytes. ``-C`` opts into a companion JSONL of per-commit path context.
"""
from __future__ import annotations

import argparse
import base64
import json
import sqlite3
import sys
import tempfile
from pathlib import Path
from typing import Any, TextIO


def path_bytes(row: dict[str, Any]) -> bytes:
    encoded = row.get("path_base64")
    if encoded is not None:
        return base64.b64decode(encoded, validate=True)
    path = row.get("path")
    if not isinstance(path, str):
        raise ValueError("path record requires path or path_base64")
    return path.encode("utf-8")


def display_path(raw: bytes) -> str:
    try:
        return raw.decode("utf-8")
    except UnicodeDecodeError:
        return "base64:" + base64.b64encode(raw).decode("ascii")


def habitat_for_path(raw: bytes) -> str:
    parts = [part for part in raw.replace(b"\\", b"/").split(b"/") if part]
    if parts and parts[0].lower() in (b"lean", b"src", b"lib"):
        parts = parts[1:]
    if len(parts) >= 2 and parts[0] == b"InfoGeometry":
        name = parts[1]
    elif parts:
        name = parts[0]
    else:
        name = b"Root"
    try:
        return name.decode("utf-8")
    except UnicodeDecodeError:
        return "base64:" + base64.b64encode(name).decode("ascii")


def _records(stream: TextIO):
    for number, line in enumerate(stream, 1):
        if line.strip():
            try:
                yield json.loads(line)
            except json.JSONDecodeError as exc:
                raise ValueError(f"invalid JSONL at line {number}: {exc}") from exc


def summarize(paths: Path, output: Path, commit_context: bool = False) -> dict[str, int]:
    output.parent.mkdir(parents=True, exist_ok=True)
    context_path = output.with_name(output.stem + ".commits.jsonl")
    with tempfile.TemporaryDirectory(prefix="evolution-habitat-") as temp_dir:
        db = sqlite3.connect(Path(temp_dir) / "habitats.sqlite3")
        db.execute("CREATE TABLE habitat_counts (habitat TEXT PRIMARY KEY, paths INTEGER NOT NULL DEFAULT 0)")
        db.execute("CREATE TABLE habitat_commits (habitat TEXT, sha TEXT, PRIMARY KEY(habitat, sha))")
        rows = 0
        context = context_path.open("w", encoding="utf-8") if commit_context else None
        try:
            with paths.open(encoding="utf-8") as source:
                for row in _records(source):
                    raw = path_bytes(row)
                    habitat = habitat_for_path(raw)
                    db.execute("INSERT INTO habitat_counts(habitat, paths) VALUES (?, 1) "
                               "ON CONFLICT(habitat) DO UPDATE SET paths = paths + 1", (habitat,))
                    sha = row.get("sha")
                    if isinstance(sha, str):
                        db.execute("INSERT OR IGNORE INTO habitat_commits VALUES (?, ?)", (habitat, sha))
                    if context is not None:
                        context.write(json.dumps({"sha": sha, "habitat": habitat,
                                                  "path": display_path(raw),
                                                  "change_type": row.get("change_type")},
                                                 ensure_ascii=False) + "\n")
                    rows += 1
            db.commit()
            report = []
            for habitat, path_count in db.execute(
                "SELECT habitat, paths FROM habitat_counts ORDER BY paths DESC, habitat"):
                commit_count = db.execute(
                    "SELECT COUNT(*) FROM habitat_commits WHERE habitat = ?", (habitat,)
                ).fetchone()[0]
                report.append({"habitat": habitat, "path_touches": path_count,
                               "commits_touched": commit_count})
            output.write_text(json.dumps(report, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
            return {"path_records": rows, "habitats": len(report),
                    "context_records": rows if commit_context else 0}
        finally:
            if context is not None:
                context.close()
            db.close()


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("paths", type=Path, help="path JSONL from evolution_extract.py")
    parser.add_argument("--out", type=Path, default=Path("evolution_habitats.json"))
    parser.add_argument("-C", "--commit-context", action="store_true",
                        help="also write per-commit path context JSONL beside --out")
    args = parser.parse_args()
    print(json.dumps(summarize(args.paths, args.out, args.commit_context), sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
