#!/usr/bin/env python3
from __future__ import annotations

import argparse
import hashlib
import json
import sys
from collections import Counter, defaultdict
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

REPO_ROOT = Path(__file__).resolve().parents[2]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from leantrail.backend.store import GraphStore
from tools.leantrail.adapters import load_snapshot


def _utc_now() -> str:
    return datetime.now(timezone.utc).isoformat()


def _iter_jsonl(path: Path) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    if not path.exists():
        return rows
    with path.open("r", encoding="utf-8") as handle:
        for line in handle:
            raw = line.strip()
            if not raw:
                continue
            try:
                obj = json.loads(raw)
            except Exception:
                continue
            if isinstance(obj, dict):
                rows.append(obj)
    return rows


def _stable_hole_id(src: str, dst: str) -> str:
    digest = hashlib.sha1(f"{src}|{dst}".encode("utf-8")).hexdigest()
    return f"hole_{digest[:24]}"


@dataclass
class HoleAccumulator:
    src: str
    dst: str
    failure_count: int = 0
    total_cost: int = 0
    error_kinds: Counter[str] | None = None
    dep_kinds: Counter[str] | None = None
    transition_ids: list[str] | None = None
    witnesses: list[str] | None = None

    def __post_init__(self) -> None:
        if self.error_kinds is None:
            self.error_kinds = Counter()
        if self.dep_kinds is None:
            self.dep_kinds = Counter()
        if self.transition_ids is None:
            self.transition_ids = []
        if self.witnesses is None:
            self.witnesses = []


def _load_required_lock_status(conformance_path: Path | None) -> dict[tuple[str, str], bool]:
    if conformance_path is None or not conformance_path.exists():
        return {}
    try:
        payload = json.loads(conformance_path.read_text(encoding="utf-8"))
    except Exception:
        return {}

    checks = payload.get("checks")
    if not isinstance(checks, list):
        return {}

    out: dict[tuple[str, str], bool] = {}
    for row in checks:
        if not isinstance(row, dict):
            continue
        if str(row.get("name", "")) != "required_path_locks":
            continue
        details = row.get("details")
        if not isinstance(details, dict):
            continue
        rows = details.get("rows")
        if not isinstance(rows, list):
            continue
        for item in rows:
            if not isinstance(item, dict):
                continue
            src = str(item.get("from", "")).strip()
            dst = str(item.get("to", "")).strip()
            if not src or not dst:
                continue
            out[(src, dst)] = bool(item.get("found", False))
    return out


def _build_holes(
    failure_rows: list[dict[str, Any]],
    *,
    max_witnesses: int,
    max_transition_ids: int,
) -> list[dict[str, Any]]:
    grouped: dict[tuple[str, str], HoleAccumulator] = {}

    for row in failure_rows:
        src = str(row.get("src", "")).strip()
        dst = str(row.get("dst", "")).strip()
        if not src or not dst:
            continue
        key = (src, dst)
        acc = grouped.get(key)
        if acc is None:
            acc = HoleAccumulator(src=src, dst=dst)
            grouped[key] = acc

        count = row.get("count")
        cost = row.get("total_cost")
        dep_kind = str(row.get("kind", "")).strip() or "depends_value"
        err_kind = str(row.get("error_kind", "")).strip() or "unknown"
        transition_id = str(row.get("id", "")).strip()

        acc.failure_count += int(count) if isinstance(count, int) and count > 0 else 1
        acc.total_cost += int(cost) if isinstance(cost, int) and cost >= 0 else 0
        acc.dep_kinds[dep_kind] += 1
        acc.error_kinds[err_kind] += 1

        if transition_id and len(acc.transition_ids) < max_transition_ids:
            acc.transition_ids.append(transition_id)

        witnesses = row.get("witnesses")
        if isinstance(witnesses, list):
            for w in witnesses:
                text = str(w).strip()
                if not text:
                    continue
                if text in acc.witnesses:
                    continue
                if len(acc.witnesses) >= max_witnesses:
                    break
                acc.witnesses.append(text)

    holes: list[dict[str, Any]] = []
    for (_, _), acc in grouped.items():
        z2 = acc.failure_count % 2
        # simple ranking shadow: weighted failure pressure + diversity of error kinds
        score = float(acc.total_cost + 2 * acc.failure_count + 3 * len(acc.error_kinds))
        holes.append(
            {
                "hole_id": _stable_hole_id(acc.src, acc.dst),
                "src": acc.src,
                "dst": acc.dst,
                "failure_count": acc.failure_count,
                "total_cost": acc.total_cost,
                "error_kinds": dict(acc.error_kinds),
                "dependency_kinds": dict(acc.dep_kinds),
                "z2_surrogate": {
                    "parity": z2,
                    "interpretation": "odd/open" if z2 == 1 else "even/pairable",
                    "basis": "failure_count mod 2",
                    "surrogate_only": True,
                },
                "priority_score": score,
                "socratic_packet": {
                    "mode": "socratic_generator",
                    "required_outputs": [
                        "missing_assumptions",
                        "bridge_obligations",
                        "minimal_lemma_chain",
                        "expected_first_error_signature",
                    ],
                    "closure_allowed": False,
                },
                "closure_contract": {
                    "mode": "closure_gate",
                    "kernel_only": True,
                },
                "evidence": {
                    "failed_transition_ids": acc.transition_ids,
                    "witnesses": acc.witnesses,
                },
                "path_state": {
                    "any": None,
                    "exclude_failed": None,
                    "locked_only": None,
                },
                "lock_requirement": {
                    "required": False,
                    "closed": None,
                },
            }
        )
    holes.sort(key=lambda row: (-float(row["priority_score"]), str(row["src"]), str(row["dst"])))
    return holes


def _annotate_paths(
    holes: list[dict[str, Any]],
    *,
    snapshot_path: Path | None,
    path_check_limit: int,
) -> None:
    if snapshot_path is None:
        return
    if not snapshot_path.exists():
        return
    try:
        snapshot = load_snapshot(snapshot_path)
    except Exception:
        return
    store = GraphStore(snapshot)

    for row in holes[: max(0, path_check_limit)]:
        src = str(row.get("src", ""))
        dst = str(row.get("dst", ""))
        if not src or not dst:
            continue
        state = row.get("path_state")
        if not isinstance(state, dict):
            continue
        try:
            state["any"] = bool(
                store.shortest_path_with_state_policy(
                    src=src, dst=dst, lawful_only=True, state_policy="any"
                ).get("found", False)
            )
            state["exclude_failed"] = bool(
                store.shortest_path_with_state_policy(
                    src=src, dst=dst, lawful_only=True, state_policy="exclude-failed"
                ).get("found", False)
            )
            state["locked_only"] = bool(
                store.shortest_path_with_state_policy(
                    src=src, dst=dst, lawful_only=True, state_policy="locked-only"
                ).get("found", False)
            )
        except Exception:
            state["any"] = None
            state["exclude_failed"] = None
            state["locked_only"] = None


def _annotate_required_locks(
    holes: list[dict[str, Any]],
    *,
    required_lock_status: dict[tuple[str, str], bool],
) -> None:
    if not required_lock_status:
        return
    for row in holes:
        src = str(row.get("src", ""))
        dst = str(row.get("dst", ""))
        key = (src, dst)
        if key not in required_lock_status:
            continue
        lock_info = row.get("lock_requirement")
        if not isinstance(lock_info, dict):
            lock_info = {}
            row["lock_requirement"] = lock_info
        lock_info["required"] = True
        lock_info["closed"] = bool(required_lock_status[key])


def _render_md(
    *,
    holes: list[dict[str, Any]],
    output_jsonl: Path,
    top_n: int,
) -> str:
    lines = [
        "# LeanTrail Hole Packet Report",
        "",
        f"- generated_at: `{_utc_now()}`",
        f"- output_jsonl: `{output_jsonl}`",
        f"- hole_count: `{len(holes)}`",
        "",
        "## Top Holes",
        "",
        "| rank | hole_id | src -> dst | failures | z2 | score | path(exclude_failed) | lock_required | lock_closed |",
        "|---:|---|---|---:|---:|---:|---|---|---|",
    ]
    for idx, row in enumerate(holes[: max(0, top_n)], start=1):
        state = row.get("path_state", {})
        lock = row.get("lock_requirement", {})
        z2 = row.get("z2_surrogate", {})
        lines.append(
            "| "
            f"{idx} | `{row.get('hole_id','')}` | "
            f"`{row.get('src','')} -> {row.get('dst','')}` | "
            f"{row.get('failure_count',0)} | "
            f"{z2.get('parity','?')} | "
            f"{row.get('priority_score',0):.1f} | "
            f"`{state.get('exclude_failed', None)}` | "
            f"`{lock.get('required', False)}` | "
            f"`{lock.get('closed', None)}` |"
        )
    return "\n".join(lines) + "\n"


def run_hole_packets(
    *,
    failed_transitions: Path,
    snapshot: Path | None,
    conformance_report: Path | None,
    out_jsonl: Path,
    out_md: Path | None,
    path_check_limit: int,
    top_n: int,
    max_witnesses: int,
    max_transition_ids: int,
) -> dict[str, Any]:
    rows = _iter_jsonl(failed_transitions)
    holes = _build_holes(
        rows,
        max_witnesses=max_witnesses,
        max_transition_ids=max_transition_ids,
    )
    _annotate_paths(
        holes,
        snapshot_path=snapshot,
        path_check_limit=path_check_limit,
    )
    lock_status = _load_required_lock_status(conformance_report)
    _annotate_required_locks(holes, required_lock_status=lock_status)

    out_jsonl.parent.mkdir(parents=True, exist_ok=True)
    with out_jsonl.open("w", encoding="utf-8") as handle:
        for row in holes:
            handle.write(json.dumps(row, ensure_ascii=True) + "\n")

    if out_md is not None:
        out_md.parent.mkdir(parents=True, exist_ok=True)
        out_md.write_text(
            _render_md(holes=holes, output_jsonl=out_jsonl, top_n=top_n),
            encoding="utf-8",
        )

    required_count = sum(1 for row in holes if bool(row.get("lock_requirement", {}).get("required", False)))
    required_closed = sum(
        1
        for row in holes
        if bool(row.get("lock_requirement", {}).get("required", False))
        and bool(row.get("lock_requirement", {}).get("closed", False))
    )
    return {
        "created_at": _utc_now(),
        "source_failed_transitions": str(failed_transitions),
        "source_snapshot": str(snapshot) if snapshot is not None else None,
        "source_conformance": str(conformance_report) if conformance_report is not None else None,
        "rows_scanned": len(rows),
        "hole_count": len(holes),
        "required_lock_holes": required_count,
        "required_lock_holes_closed": required_closed,
        "output_jsonl": str(out_jsonl),
        "output_md": str(out_md) if out_md is not None else None,
    }


def _parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Build ranked hole packets from LeanTrail failure memory "
            "and conformance surfaces."
        )
    )
    parser.add_argument(
        "--failed-transitions",
        default="artifacts/leantrail/failed_transitions.jsonl",
        help="Input failed transitions JSONL.",
    )
    parser.add_argument(
        "--snapshot",
        default="artifacts/leantrail/graph_snapshot.json",
        help="Optional snapshot for path-state annotation.",
    )
    parser.add_argument(
        "--conformance-report",
        default="artifacts/leantrail/conformance_lock_gate.json",
        help="Optional conformance JSON for required-lock status annotation.",
    )
    parser.add_argument(
        "--out",
        default="artifacts/leantrail/hole_packets.jsonl",
        help="Output hole packets JSONL.",
    )
    parser.add_argument(
        "--md-out",
        default="artifacts/leantrail/hole_packets.md",
        help="Optional markdown report output.",
    )
    parser.add_argument(
        "--json-out",
        default="artifacts/leantrail/hole_packets_report.json",
        help="Operation report JSON output.",
    )
    parser.add_argument(
        "--path-check-limit",
        type=int,
        default=300,
        help="Compute path-state annotations for at most this many top holes.",
    )
    parser.add_argument(
        "--top-n",
        type=int,
        default=40,
        help="Top-N rows shown in markdown summary.",
    )
    parser.add_argument(
        "--max-witnesses",
        type=int,
        default=8,
        help="Maximum witness strings retained per hole.",
    )
    parser.add_argument(
        "--max-transition-ids",
        type=int,
        default=16,
        help="Maximum transition ids retained per hole.",
    )
    return parser.parse_args()


def main() -> int:
    args = _parse_args()
    failed_transitions = Path(args.failed_transitions).resolve()
    if not failed_transitions.exists():
        raise FileNotFoundError(f"Failed transitions not found: {failed_transitions}")

    snapshot_arg = str(args.snapshot).strip() if args.snapshot is not None else ""
    snapshot = Path(snapshot_arg).resolve() if snapshot_arg else None
    if snapshot is not None and not snapshot.exists():
        snapshot = None

    conformance_arg = str(args.conformance_report).strip() if args.conformance_report is not None else ""
    conformance_report = Path(conformance_arg).resolve() if conformance_arg else None
    if conformance_report is not None and not conformance_report.exists():
        conformance_report = None

    out_jsonl = Path(args.out).resolve()
    md_arg = str(args.md_out).strip() if args.md_out is not None else ""
    out_md = Path(md_arg).resolve() if md_arg else None
    report_out = Path(args.json_out).resolve()

    report = run_hole_packets(
        failed_transitions=failed_transitions,
        snapshot=snapshot,
        conformance_report=conformance_report,
        out_jsonl=out_jsonl,
        out_md=out_md,
        path_check_limit=max(0, int(args.path_check_limit)),
        top_n=max(0, int(args.top_n)),
        max_witnesses=max(1, int(args.max_witnesses)),
        max_transition_ids=max(1, int(args.max_transition_ids)),
    )
    report_out.parent.mkdir(parents=True, exist_ok=True)
    report_out.write_text(json.dumps(report, indent=2, ensure_ascii=True) + "\n", encoding="utf-8")
    print(
        "Hole packets written:",
        report["output_jsonl"],
        f"(holes={report['hole_count']}, required_locks_closed={report['required_lock_holes_closed']}/{report['required_lock_holes']})",
    )
    if report.get("output_md"):
        print(f"Hole report markdown written: {report['output_md']}")
    print(f"Operation report written: {report_out}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
