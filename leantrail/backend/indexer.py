from __future__ import annotations

import argparse
import json
from pathlib import Path

from .extractor import run_refresh_pipeline
from .normalizer import LeanTrailNormalizer


def build_snapshot(
    repo_root: Path,
    snapshot_out: Path,
    refresh: bool = False,
    max_process_events: int | None = None,
) -> Path:
    repo_root = repo_root.resolve()
    if refresh:
        run_refresh_pipeline(repo_root)

    normalizer = LeanTrailNormalizer(repo_root)
    snapshot = normalizer.build_snapshot(max_process_events=max_process_events)

    snapshot_out.parent.mkdir(parents=True, exist_ok=True)
    snapshot_out.write_text(json.dumps(snapshot.to_dict(), indent=2, ensure_ascii=True) + "\n", encoding="utf-8")
    return snapshot_out


def _parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Build LeanTrail normalized graph snapshot.")
    parser.add_argument(
        "--repo-root",
        default=".",
        help="Repository root.",
    )
    parser.add_argument(
        "--snapshot-out",
        default="artifacts/leantrail/graph_snapshot.json",
        help="Output snapshot JSON path.",
    )
    parser.add_argument(
        "--refresh",
        action="store_true",
        help="Run the locked extractor pipeline before normalization.",
    )
    parser.add_argument(
        "--max-process-events",
        type=int,
        default=None,
        help="Optional cap when ingesting process-flow events.",
    )
    return parser.parse_args()


def main() -> int:
    args = _parse_args()
    repo_root = Path(args.repo_root)
    snapshot_out = Path(args.snapshot_out)
    out = build_snapshot(
        repo_root=repo_root,
        snapshot_out=snapshot_out,
        refresh=args.refresh,
        max_process_events=args.max_process_events,
    )
    print(f"LeanTrail snapshot written: {out}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
