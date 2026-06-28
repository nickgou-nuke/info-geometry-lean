#!/usr/bin/env python3
"""Batch Lean syntax-tree export across repo-owned and mathlib Lean sources.

This wraps `tools/leantrail/DumpLeanGraph.lean`, which exports syntax JSONL for
individual files. The wrapper expands directory roots into `.lean` files and
streams the concatenated syntax records into one output file.

The export is file-level syntax evidence only. It does not claim elaborated
proof dependencies or declaration truth; those are handled by the separate
declaration/type export lanes.
"""

from __future__ import annotations

import argparse
import subprocess
import sys
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[2]
DEFAULT_ROOTS = [
    REPO_ROOT / "lean",
    REPO_ROOT / ".lake" / "packages" / "mathlib" / "Mathlib",
]


def collect_lean_files(root: Path) -> list[Path]:
    if not root.exists():
        return []
    return sorted(p for p in root.rglob("*.lean") if p.is_file())


def run_dump(files: list[Path]) -> subprocess.CompletedProcess[str]:
    cmd = ["lake", "env", "lean", "--run", "tools/leantrail/DumpLeanGraph.lean", "--quiet", *map(str, files)]
    return subprocess.run(cmd, cwd=REPO_ROOT, text=True, capture_output=True)


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument(
        "--root",
        action="append",
        type=Path,
        help="Root directory to scan for `.lean` files. May be repeated.",
    )
    ap.add_argument(
        "--out",
        type=Path,
        default=Path("artifacts/leantrail/batch_syntax_dump.jsonl"),
        help="Output JSONL path for concatenated syntax records.",
    )
    ap.add_argument(
        "--chunk-size",
        type=int,
        default=24,
        help="Number of Lean files to send to each `DumpLeanGraph` invocation.",
    )
    args = ap.parse_args()

    roots = args.root or DEFAULT_ROOTS
    files: list[Path] = []
    for root in roots:
        files.extend(collect_lean_files(root))
    files = sorted(dict.fromkeys(files))
    if not files:
        raise SystemExit("batch_dump_syntax: no Lean files found")

    args.out.parent.mkdir(parents=True, exist_ok=True)
    with args.out.open("w", encoding="utf-8") as out:
        for start in range(0, len(files), max(1, args.chunk_size)):
            batch = files[start:start + max(1, args.chunk_size)]
            proc = run_dump(batch)
            if proc.stderr:
                sys.stderr.write(proc.stderr)
            if proc.returncode != 0:
                raise SystemExit(proc.returncode)
            out.write(proc.stdout)

    print(f"batch_dump_syntax: wrote {args.out} from {len(files)} files", flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
