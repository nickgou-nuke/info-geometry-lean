#!/usr/bin/env python3
from __future__ import annotations

import argparse
import sys
from pathlib import Path

if __package__ in (None, ""):
    sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
    from tools.infra.build import run_locked_lake_build
else:
    from tools.infra.build import run_locked_lake_build


STATE_FIRST_TARGETS = [
    "InfoGeometry.Canonical.OperatorialCramerRaoStateFirstChunk1",
    "InfoGeometry.Canonical.OperatorialCramerRaoStateFirstChunk2",
    "InfoGeometry.Canonical.OperatorialCramerRaoStateFirstChunk3",
    "InfoGeometry.Canonical.OperatorialCramerRaoStateFirstChunk4",
    "InfoGeometry.Canonical.OperatorialCramerRaoStateFirstSemanticAudit",
]


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Build the state-first canonical lane (Chunk1..4 + semantic audit) under the shared build lock."
    )
    parser.add_argument(
        "--wait-for-build-lock",
        action="store_true",
        help="Block until the shared build lock is available instead of failing immediately.",
    )
    parser.add_argument(
        "--wfail",
        action="store_true",
        help="Pass --wfail to lake build (treat warnings as errors).",
    )
    parser.add_argument(
        "--include-canonical-all",
        action="store_true",
        help="Also build InfoGeometry.Canonical.All after the state-first targets.",
    )
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    targets = list(STATE_FIRST_TARGETS)
    if args.include_canonical_all:
        targets.append("InfoGeometry.Canonical.All")
    return run_locked_lake_build(
        targets, wait_for_lock=args.wait_for_build_lock, wfail=args.wfail
    )


if __name__ == "__main__":
    raise SystemExit(main())

