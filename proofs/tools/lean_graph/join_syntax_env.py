#!/usr/bin/env python3
"""Join DumpLeanGraph syntax JSONL with ExtractGraph environment JSON.

The bridge is intentionally conservative: it matches declarations by exact
fully-qualified name and annotates each syntax declaration with the environment
kind/dependencies when available.
"""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Any


def fail(message: str) -> None:
    raise SystemExit(f"join_syntax_env: {message}")


def load_syntax_jsonl(path: Path) -> list[dict[str, Any]]:
    records: list[dict[str, Any]] = []
    with path.open(encoding="utf-8") as handle:
        for line_number, line in enumerate(handle, start=1):
            line = line.strip()
            if not line:
                continue
            try:
                record = json.loads(line)
            except json.JSONDecodeError as exc:
                fail(f"{path}:{line_number}: invalid JSONL: {exc}")
            if record.get("layer") != "syntax":
                fail(f"{path}:{line_number}: expected layer='syntax'")
            name = record.get("name")
            if not isinstance(name, str) or not name:
                fail(f"{path}:{line_number}: missing syntax name")
            records.append(record)
    if not records:
        fail(f"{path}: no syntax records")
    return records


def load_env_json(path: Path) -> dict[str, dict[str, Any]]:
    try:
        raw = json.loads(path.read_text(encoding="utf-8"))
    except json.JSONDecodeError as exc:
        fail(f"{path}: invalid environment JSON: {exc}")
    if not isinstance(raw, list):
        fail(f"{path}: expected environment JSON array")
    env: dict[str, dict[str, Any]] = {}
    for index, record in enumerate(raw):
        if not isinstance(record, dict):
            fail(f"{path}: env record {index} must be an object")
        name = record.get("name")
        if not isinstance(name, str) or not name:
            fail(f"{path}: env record {index} missing name")
        env[name] = record
    return env


def syntax_range(record: dict[str, Any]) -> Any:
    syntax = record.get("syntax")
    if not isinstance(syntax, dict):
        return None
    return syntax.get("range")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--syntax-jsonl", required=True, type=Path)
    parser.add_argument("--env-json", required=True, type=Path)
    parser.add_argument("--require-match", action="append", default=[])
    parser.add_argument(
        "--include-syntax-tree",
        action="store_true",
        help="include the full syntax tree in each bridge record for full graph import",
    )
    args = parser.parse_args()

    syntax_records = load_syntax_jsonl(args.syntax_jsonl)
    env_records = load_env_json(args.env_json)

    matched_names: set[str] = set()
    for syntax in syntax_records:
        name = syntax["name"]
        env = env_records.get(name)
        if env is not None:
            matched_names.add(name)
        bridge = {
            "layer": "syntax_env_bridge",
            "name": name,
            "matched": env is not None,
            "syntax": {
                "keyword": syntax.get("keyword"),
                "range": syntax_range(syntax),
            },
            "env": None
            if env is None
            else {
                "kind": env.get("kind"),
                "deps": env.get("deps", []),
            },
        }
        if args.include_syntax_tree:
            bridge["syntaxTree"] = syntax.get("syntax")
        print(json.dumps(bridge, ensure_ascii=False, separators=(",", ":")))

    for required in args.require_match:
        if required not in matched_names:
            fail(f"required declaration did not match environment: {required}")
    print(
        f"joined {len(syntax_records)} syntax records; "
        f"matched {len(matched_names)} against {len(env_records)} env records",
        file=sys.stderr,
    )


if __name__ == "__main__":
    main()
