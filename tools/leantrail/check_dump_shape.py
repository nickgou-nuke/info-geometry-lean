#!/usr/bin/env python3
"""Validate `DumpLeanGraph.lean` syntax JSONL shape."""

from __future__ import annotations

import argparse
import json
import sys
from typing import Any

VALID_KINDS = {"node", "atom", "ident"}


def fail(message: str) -> None:
    raise SystemExit(f"check_dump_shape: {message}")


def check_range(value: Any, path: str) -> None:
    if value is None:
        return
    if not isinstance(value, dict):
        fail(f"{path}.range must be object or null")
    for key in ("startLine", "startCol", "endLine", "endCol"):
        if not isinstance(value.get(key), int):
            fail(f"{path}.range.{key} must be an integer")


def check_syntax(value: Any, path: str = "syntax") -> None:
    if not isinstance(value, dict):
        fail(f"{path} must be an object")
    kind = value.get("kind")
    if kind not in VALID_KINDS:
        fail(f"{path}.kind must be one of {sorted(VALID_KINDS)}")
    if not isinstance(value.get("syntaxKind"), str):
        fail(f"{path}.syntaxKind must be a string")
    check_range(value.get("range"), path)
    if kind == "node":
        children = value.get("children")
        if not isinstance(children, list):
            fail(f"{path}.children must be a list")
        for index, child in enumerate(children):
            check_syntax(child, f"{path}.children[{index}]")
    elif kind == "atom":
        if not isinstance(value.get("value"), str):
            fail(f"{path}.value must be a string")
    elif kind == "ident":
        if not isinstance(value.get("raw"), str):
            fail(f"{path}.raw must be a string")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--expect-name", action="append", default=[])
    parser.add_argument("--expect-keyword", action="append", default=[])
    args = parser.parse_args()

    names: set[str] = set()
    keywords: set[str] = set()
    count = 0
    for line_number, line in enumerate(sys.stdin, start=1):
        line = line.strip()
        if not line:
            continue
        try:
            record = json.loads(line)
        except json.JSONDecodeError as exc:
            fail(f"line {line_number} is not valid JSON: {exc}")
        if record.get("layer") != "syntax":
            fail(f"line {line_number}: layer must be 'syntax'")
        name = record.get("name")
        keyword = record.get("keyword")
        if not isinstance(name, str) or not name:
            fail(f"line {line_number}: name must be a nonempty string")
        if not isinstance(keyword, str) or not keyword:
            fail(f"line {line_number}: keyword must be a nonempty string")
        check_syntax(record.get("syntax"), f"line[{line_number}].syntax")
        names.add(name)
        keywords.add(keyword)
        count += 1

    if count == 0:
        fail("no records read")
    for expected in args.expect_name:
        if expected not in names:
            fail(f"missing expected declaration name: {expected}")
    for expected in args.expect_keyword:
        if expected not in keywords:
            fail(f"missing expected keyword: {expected}")
    print(f"validated {count} syntax records", file=sys.stderr)


if __name__ == "__main__":
    main()
