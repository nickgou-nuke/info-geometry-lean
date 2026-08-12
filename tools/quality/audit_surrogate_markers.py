#!/usr/bin/env python3
"""Check stable Lean code for surrogate marker tokens.

Comments and string literals are explanatory text, not executable surrogate
constructs, so they are removed before scanning.  The shell gate remains the
policy owner; this helper only makes its lexical scope precise.
"""

from __future__ import annotations

import argparse
import re
from pathlib import Path


MARKER_RE = re.compile(r"\b(?:placeholder|surrogate)\b", re.IGNORECASE)
EXCLUDED_PARTS = {"Unstable", "Archive", "tmp"}
EXCLUDED_NAMES = {"All.lean", "CoverageClosure.lean", "tmp.lean"}


def strip_comments_and_strings(text: str) -> str:
    out: list[str] = []
    i = 0
    block_depth = 0
    in_string = False
    while i < len(text):
        if block_depth:
            if text.startswith("/-", i):
                block_depth += 1
                out.extend((" ", " "))
                i += 2
            elif text.startswith("-/", i):
                block_depth -= 1
                out.extend((" ", " "))
                i += 2
            else:
                ch = text[i]
                out.append("\n" if ch == "\n" else " ")
                i += 1
            continue

        if in_string:
            ch = text[i]
            out.append("\n" if ch == "\n" else " ")
            i += 1
            if ch == "\\" and i < len(text):
                out.append("\n" if text[i] == "\n" else " ")
                i += 1
            elif ch == '"':
                in_string = False
            continue

        if text.startswith("--", i):
            while i < len(text) and text[i] != "\n":
                out.append(" ")
                i += 1
            continue
        if text.startswith("/-", i):
            block_depth = 1
            out.extend((" ", " "))
            i += 2
            continue
        ch = text[i]
        out.append(ch)
        i += 1
        if ch == '"':
            in_string = True
    return "".join(out)


def iter_stable_files(root: Path):
    for path in sorted((root / "lean").rglob("*.lean")):
        if not path.is_file():
            continue
        if path.name in EXCLUDED_NAMES or EXCLUDED_PARTS.intersection(path.parts):
            continue
        yield path


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--root", type=Path, default=Path.cwd())
    args = parser.parse_args()
    root = args.root.resolve()
    failures = 0
    for path in iter_stable_files(root):
        code = strip_comments_and_strings(path.read_text(errors="ignore"))
        for line_no, line in enumerate(code.splitlines(), 1):
            if MARKER_RE.search(line):
                print(f"{path.relative_to(root)}:{line_no}: {line.strip()}")
                failures += 1
    return 1 if failures else 0


if __name__ == "__main__":
    raise SystemExit(main())
