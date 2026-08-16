#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import re
from pathlib import Path
from typing import Any

ALLOWED_TYPES = {
    "section",
    "definition",
    "lemma",
    "theorem",
    "proof",
    "remark",
    "equation",
    "paragraph",
    "appendix",
}

BEGIN_ENV_RE = re.compile(r"\\begin\{([^}]+)\}")
END_ENV_RE = re.compile(r"\\end\{([^}]+)\}")
LABEL_RE = re.compile(r"\\label\{([^}]+)\}")
INLINE_DOLLAR_RE = re.compile(r"(?<!\\)\$")
DISPLAY_BRACKET_OPEN_RE = re.compile(r"\\\[")
DISPLAY_BRACKET_CLOSE_RE = re.compile(r"\\\]")
INLINE_PAREN_OPEN_RE = re.compile(r"\\\(")
INLINE_PAREN_CLOSE_RE = re.compile(r"\\\)")


# [lossless-compact] load_json folded into igf.common.json_io.load_json
from igf.common.json_io import load_json


def build_math_env_state(lines: list[str]) -> list[dict[str, Any]]:
    states: list[dict[str, Any]] = []
    env_stack: list[str] = []
    in_display_bracket = False
    in_inline_paren = False
    in_dollar_math = False

    for line in lines:
        states.append(
            {
                "env_depth": len(env_stack),
                "in_display_bracket": in_display_bracket,
                "in_inline_paren": in_inline_paren,
                "in_dollar_math": in_dollar_math,
            }
        )

        for match in BEGIN_ENV_RE.finditer(line):
            env_stack.append(match.group(1))
        for match in END_ENV_RE.finditer(line):
            if env_stack and env_stack[-1] == match.group(1):
                env_stack.pop()

        opens = len(DISPLAY_BRACKET_OPEN_RE.findall(line))
        closes = len(DISPLAY_BRACKET_CLOSE_RE.findall(line))
        if opens > closes:
            in_display_bracket = True
        elif closes > opens:
            in_display_bracket = False

        opens = len(INLINE_PAREN_OPEN_RE.findall(line))
        closes = len(INLINE_PAREN_CLOSE_RE.findall(line))
        if opens > closes:
            in_inline_paren = True
        elif closes > opens:
            in_inline_paren = False

        dollar_count = len(INLINE_DOLLAR_RE.findall(line))
        if dollar_count % 2 == 1:
            in_dollar_math = not in_dollar_math

    states.append(
        {
            "env_depth": len(env_stack),
            "in_display_bracket": in_display_bracket,
            "in_inline_paren": in_inline_paren,
            "in_dollar_math": in_dollar_math,
        }
    )
    return states


def validate(source_path: Path, chunks_path: Path) -> tuple[list[str], list[str]]:
    source_lines = source_path.read_text(encoding="utf-8").splitlines()
    n = len(source_lines)
    data = load_json(chunks_path)

    errors: list[str] = []
    warnings: list[str] = []

    for key in ("document_id", "source_path", "chunks"):
        if key not in data:
            errors.append(f"missing top-level key: {key}")

    chunks = data.get("chunks")
    if not isinstance(chunks, list):
        errors.append("chunks must be a list")
        return errors, warnings

    states = build_math_env_state(source_lines)

    last_end = 0
    ids: set[str] = set()
    covered = [False] * n

    for i, chunk in enumerate(chunks, start=1):
        prefix = f"chunk[{i}]"
        if not isinstance(chunk, dict):
            errors.append(f"{prefix} must be object")
            continue

        for k in ("id", "type", "start_line", "end_line", "anchors", "context_header"):
            if k not in chunk:
                errors.append(f"{prefix} missing key: {k}")

        cid = chunk.get("id")
        ctype = chunk.get("type")
        start = chunk.get("start_line")
        end = chunk.get("end_line")

        if not isinstance(cid, str) or not cid.strip():
            errors.append(f"{prefix}.id must be non-empty string")
        elif cid in ids:
            errors.append(f"duplicate chunk id: {cid}")
        else:
            ids.add(cid)

        if ctype not in ALLOWED_TYPES:
            errors.append(f"{prefix}.type invalid: {ctype}")

        if not isinstance(start, int) or not isinstance(end, int):
            errors.append(f"{prefix}.start_line/end_line must be int")
            continue
        if start < 1 or end < 1 or start > end or end > n:
            errors.append(f"{prefix} invalid range {start}-{end} for source lines {n}")
            continue
        if start <= last_end:
            errors.append(f"{prefix} overlaps or is out of order: start={start} last_end={last_end}")
        last_end = end

        for ln in range(start - 1, end):
            covered[ln] = True

        entry_state = states[start - 1]
        exit_state = states[end]
        if entry_state["env_depth"] > 0 or entry_state["in_display_bracket"] or entry_state["in_inline_paren"] or entry_state["in_dollar_math"]:
            errors.append(f"{prefix} starts inside open math/env context at line {start}")
        if entry_state != exit_state:
            errors.append(f"{prefix} changes open math/env state across boundary ({start}-{end})")

        anchors = chunk.get("anchors")
        if not isinstance(anchors, dict):
            errors.append(f"{prefix}.anchors must be object")
        else:
            label = anchors.get("label")
            if isinstance(label, str) and label:
                span = "\n".join(source_lines[start - 1 : end])
                if f"\\label{{{label}}}" not in span:
                    warnings.append(f"{prefix} anchor label not found in span: {label}")

        dependencies = chunk.get("dependencies", [])
        if not isinstance(dependencies, list):
            errors.append(f"{prefix}.dependencies must be list")
        else:
            for dep in dependencies:
                if not isinstance(dep, str):
                    errors.append(f"{prefix}.dependencies contains non-string")
                elif dep not in ids:
                    warnings.append(f"{prefix} dependency not yet seen (or missing): {dep}")

        size = end - start + 1
        if size < 40 and ctype not in {"equation", "remark"}:
            warnings.append(f"{prefix} small chunk size ({size} lines)")
        if size > 320:
            warnings.append(f"{prefix} large chunk size ({size} lines)")

    uncovered_nonempty = [i + 1 for i, (is_cov, line) in enumerate(zip(covered, source_lines)) if (not is_cov and line.strip())]
    if uncovered_nonempty:
        warnings.append(
            f"uncovered non-empty lines: {len(uncovered_nonempty)} (first 20: {uncovered_nonempty[:20]})"
        )

    return errors, warnings


def main() -> int:
    parser = argparse.ArgumentParser(description="Validate semantic chunk JSON against source text.")
    parser.add_argument("--source", type=Path, required=True)
    parser.add_argument("--chunks", type=Path, required=True)
    parser.add_argument("--json", action="store_true")
    args = parser.parse_args()

    errors, warnings = validate(args.source, args.chunks)
    payload = {
        "status": "FAIL" if errors else ("WARN" if warnings else "PASS"),
        "errors": errors,
        "warnings": warnings,
        "source": str(args.source),
        "chunks": str(args.chunks),
    }

    if args.json:
        print(json.dumps(payload, indent=2, ensure_ascii=False))
    else:
        print(f"status: {payload['status']}")
        if errors:
            print("errors:")
            for e in errors:
                print(f"- {e}")
        if warnings:
            print("warnings:")
            for w in warnings:
                print(f"- {w}")

    return 1 if errors else 0


if __name__ == "__main__":
    raise SystemExit(main())
