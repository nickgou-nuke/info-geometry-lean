#!/usr/bin/env python3
"""Normalize DumpLeanGraph v1 records into a compact declaration index.

Input: JSONL from DumpLeanGraph.lean.
Output: JSONL with one compact record per top-level declaration.

This is intentionally syntax-only: it preserves parser names/keywords/ranges and
does not claim elaborated identifier resolution or semantic dependency edges.
"""

from __future__ import annotations

import json
import sys
from typing import Any


def fail(message: str) -> None:
    raise SystemExit(f"normalize_syntax_index: {message}")


def decl_range(record: dict[str, Any]) -> Any:
    syntax = record.get("syntax")
    if not isinstance(syntax, dict):
        return None
    return syntax.get("range")


def main() -> None:
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
            fail(f"line {line_number}: expected layer='syntax'")
        name = record.get("name")
        keyword = record.get("keyword")
        if not isinstance(name, str) or not name:
            fail(f"line {line_number}: missing declaration name")
        if not isinstance(keyword, str) or not keyword:
            fail(f"line {line_number}: missing declaration keyword")
        normalized = {
            "layer": "syntax_decl",
            "_key": name.replace(".", "__").replace("`", "_").replace("«", "").replace("»", ""),
            "name": name,
            "keyword": keyword,
            "range": decl_range(record),
        }
        print(json.dumps(normalized, ensure_ascii=False, separators=(",", ":")))
        count += 1
    print(f"normalized {count} syntax declarations", file=sys.stderr)


if __name__ == "__main__":
    main()
