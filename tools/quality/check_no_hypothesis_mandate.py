#!/usr/bin/env python3
from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path

if __package__ in (None, ""):
    sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
    from tools.pathing import normalize_user_path, repo_root
else:
    from tools.pathing import normalize_user_path, repo_root


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


def strip_lean_comments(text: str) -> str:
    """Remove Lean line/block comments before checking proof-hole tokens."""
    out: list[str] = []
    i = 0
    depth = 0
    while i < len(text):
        if depth:
            if text.startswith("/-", i):
                depth += 1
                out.extend("  ")
                i += 2
            elif text.startswith("-/", i):
                depth -= 1
                out.extend("  ")
                i += 2
            else:
                out.append("\n" if text[i] == "\n" else " ")
                i += 1
        elif text.startswith("/-", i):
            depth = 1
            out.extend("  ")
            i += 2
        elif text.startswith("--", i):
            while i < len(text) and text[i] != "\n":
                out.append(" ")
                i += 1
        else:
            out.append(text[i])
            i += 1
    return "".join(out)


def parse_args() -> argparse.Namespace:
    p = argparse.ArgumentParser(
        description=(
            "Hard gate for anti-hypothesis policy: bans witness/assumption naming "
            "and proof-hole tokens in Lean declarations."
        )
    )
    p.add_argument("--root", default=str(DEFAULT_ROOT.relative_to(ROOT)))
    return p.parse_args()


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
        text = path.read_text(encoding="utf-8")
        code = strip_lean_comments(text)
        if BAD_BODY_RE.search(code):
            failures.append(f"{path}: banned proof-hole token found")
        for i, line in enumerate(text.splitlines(), start=1):
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
