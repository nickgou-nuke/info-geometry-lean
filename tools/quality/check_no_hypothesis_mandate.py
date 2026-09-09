#!/usr/bin/env python3
from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path

if __package__ in (None, ""):
    sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
    from tools.pathing import normalize_user_path, repo_root
    from tools.quality.common import strip_lean_comments
else:
    from tools.pathing import normalize_user_path, repo_root
    from tools.quality.common import strip_lean_comments


ROOT = repo_root()
DEFAULT_ROOT = ROOT / "lean" / "InfoGeometry"

DECL_RE = re.compile(r"^\s*(theorem|lemma|def|structure)\s+([A-Za-z0-9_'.]+)")
# Concrete `witness` and `certificate` names can describe honest, proved
# constructions.  The hard gate targets names that advertise injected
# assumptions or placeholder proofs.
BAD_NAME_RE = re.compile(
    r"(?:^|_)(?:hypothesis|assumption|axiom|postulate)(?:_|$)"
)
# Honest open debt is allowed via `sorry`; non-honest placeholders remain banned.
BAD_BODY_RE = re.compile(r"\b(admit|axiom|postulate)\b")


def parse_args() -> argparse.Namespace:
    p = argparse.ArgumentParser(
        description=(
            "Hard gate for anti-hypothesis policy: bans witness/assumption naming "
            "and proof-hole tokens in Lean declarations."
        )
    )
    p.add_argument("--root", default=str(DEFAULT_ROOT.relative_to(ROOT)))
    return p.parse_args()


def strip_lean_strings(source: str) -> str:
    out: list[str] = []
    in_str = False
    in_char = False
    i = 0
    n = len(source)
    while i < n:
        ch = source[i]
        if in_str:
            if ch == "\\" and i + 1 < n:
                out.extend([" ", " "])
                i += 2
                continue
            if ch == '"':
                in_str = False
            out.append("\n" if ch == "\n" else " ")
            i += 1
            continue
        if in_char:
            if ch == "\\" and i + 1 < n:
                out.extend([" ", " "])
                i += 2
                continue
            if ch == "'":
                in_char = False
            out.append("\n" if ch == "\n" else " ")
            i += 1
            continue
        if ch == '"':
            in_str = True
            out.append(" ")
            i += 1
            continue
        if ch == "'" and i + 2 < n and source[i + 2] == "'":
            in_char = True
            out.append(" ")
            i += 1
            continue
        out.append(ch)
        i += 1
    return "".join(out)


def main() -> int:
    args = parse_args()
    scan_root = normalize_user_path(args.root, ROOT / args.root)
    if not scan_root.exists():
        print(f"[no-hypothesis-gate] missing root: {scan_root}")
        return 1

    failures: list[str] = []
    for path in sorted(scan_root.rglob("*.lean")):
        if any(x in str(path) for x in ["/lake-packages/", "/.lake/", "/archive/"]):
            continue
        # Repository snapshots may contain tracked links into an external
        # checkout.  A broken link is not a Lean source file and must not make
        # this lexical gate fail before it reaches repo-owned declarations.
        if path.is_symlink() and not path.exists():
            continue
        text = path.read_text(encoding="utf-8")
        code = strip_lean_comments(text, preserve_lines=True)
        code_no_str = strip_lean_strings(code)
        for i, line in enumerate(code_no_str.splitlines(), start=1):
            if BAD_BODY_RE.search(line):
                failures.append(f"{path}:{i}: banned proof-hole token found in line: {line.strip()}")
            m = DECL_RE.match(line)
            if not m:
                continue
            kind, name = m.group(1), m.group(2)
            if BAD_NAME_RE.search(name):
                failures.append(f"{path}:{i}: {kind} `{name}` uses banned name pattern")

    if failures:
        print("[no-hypothesis-gate] FAILED")
        for f in failures:
            print(f"  - {f}")
        return 1
    print("[no-hypothesis-gate] PASSED")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
