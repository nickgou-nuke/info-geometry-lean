#!/usr/bin/env python3
"""Phase 7 Optional Linter: Heartbeat & Performance Guard Auditor for Hot Operator-Algebra Paths.

Scans Lean files for excessive `maxHeartbeats` overrides (`set_option maxHeartbeats ...`)
and reports declarations on hot operator-algebra paths where `#count_heartbeats` profiling
or lemma decomposition is recommended.
"""

from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
MAX_HEARTBEATS_RE = re.compile(r"set_option\s+maxHeartbeats\s+(\d+)")
COUNT_HEARTBEATS_RE = re.compile(r"#count_heartbeats\b")


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument(
        "paths",
        nargs="*",
        default=["lean/InfoGeometry/OperatorAlgebra", "lean/InfoGeometry/Canonical"],
        help="Lean files or directories to scan.",
    )
    ap.add_argument(
        "--threshold",
        type=int,
        default=400000,
        help="Warn when `set_option maxHeartbeats N` exceeds this threshold (default: 400000).",
    )
    ap.add_argument("--strict", action="store_true", help="Exit 1 if any override exceeds --threshold.")
    args = ap.parse_args()

    files: list[Path] = []
    for raw in args.paths:
        p = Path(raw) if Path(raw).is_absolute() else ROOT / raw
        if p.is_file() and p.suffix == ".lean":
            files.append(p)
        elif p.is_dir():
            files.extend(sorted(p.rglob("*.lean")))

    high_overrides: list[str] = []
    guarded_count = 0

    for path in sorted(set(files)):
        text = path.read_text(encoding="utf-8", errors="ignore")
        rel = path.resolve().relative_to(ROOT).as_posix()
        if COUNT_HEARTBEATS_RE.search(text):
            guarded_count += 1
        for idx, line in enumerate(text.splitlines(), 1):
            m = MAX_HEARTBEATS_RE.search(line)
            if m:
                val = int(m.group(1))
                if val > args.threshold:
                    high_overrides.append(f"{rel}:{idx}: maxHeartbeats={val} (> {args.threshold})")

    print(
        f"[heartbeat_guard] scanned {len(set(files))} file(s); "
        f"#count_heartbeats guards={guarded_count}; "
        f"overrides > {args.threshold}: {len(high_overrides)}"
    )
    for item in high_overrides[:50]:
        print(f"  - {item}")

    if args.strict and high_overrides:
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
