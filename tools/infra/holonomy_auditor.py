#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import sys
from datetime import datetime, timezone
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from leantrail.backend.models import GraphSnapshot
from leantrail.backend.store import GraphStore


def _utc_now() -> str:
    return datetime.now(timezone.utc).isoformat()


def run_holonomy_audit(
    snapshot_path: Path,
    out_path: Path,
    *,
    limit: int,
    alpha: float,
    beta: float,
    gamma: float,
    min_score: float,
) -> dict[str, object]:
    payload = json.loads(snapshot_path.read_text(encoding="utf-8"))
    snapshot = GraphSnapshot.from_dict(payload)
    store = GraphStore(snapshot)

    hotspots = store.holonomy_hotspots(
        limit=limit,
        alpha=alpha,
        beta=beta,
        gamma=gamma,
        min_score=min_score,
    )

    report: dict[str, object] = {
        "created_at": _utc_now(),
        "source": "tools.infra.holonomy_auditor",
        "snapshot": str(snapshot_path),
        "weights": {"alpha": alpha, "beta": beta, "gamma": gamma},
        "min_score": min_score,
        "count": len(hotspots),
        "hotspots": hotspots,
    }
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(json.dumps(report, indent=2, ensure_ascii=True) + "\n", encoding="utf-8")
    return report


def _parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Compute LeanTrail holonomy hotspots from a normalized snapshot. "
            "Uses telemetry fields when present, otherwise falls back to structural proxies."
        )
    )
    parser.add_argument(
        "--snapshot",
        default="artifacts/leantrail/graph_snapshot.json",
        help="Path to LeanTrail graph snapshot.",
    )
    parser.add_argument(
        "--out",
        default="artifacts/leantrail/holonomy_report.json",
        help="Output JSON report path.",
    )
    parser.add_argument("--limit", type=int, default=25, help="Maximum hotspot rows.")
    parser.add_argument("--alpha", type=float, default=1.5, help="Tactic-step weight.")
    parser.add_argument("--beta", type=float, default=2.0, help="Context-expansion weight.")
    parser.add_argument("--gamma", type=float, default=3.0, help="Metavariable-flux weight.")
    parser.add_argument("--min-score", type=float, default=0.0, help="Filter threshold.")
    return parser.parse_args()


def main() -> int:
    args = _parse_args()
    snapshot_path = Path(args.snapshot).resolve()
    out_path = Path(args.out).resolve()

    if not snapshot_path.exists():
        raise FileNotFoundError(
            f"Snapshot not found: {snapshot_path}. "
            "Run `python3 -m leantrail.backend.indexer --snapshot-out artifacts/leantrail/graph_snapshot.json` first."
        )

    report = run_holonomy_audit(
        snapshot_path=snapshot_path,
        out_path=out_path,
        limit=args.limit,
        alpha=args.alpha,
        beta=args.beta,
        gamma=args.gamma,
        min_score=args.min_score,
    )
    print(
        "Holonomy audit written:",
        out_path,
        f"(rows={report['count']}, alpha={args.alpha}, beta={args.beta}, gamma={args.gamma})",
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
