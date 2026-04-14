#!/usr/bin/env python3
"""Compute injection-pipeline SLO metrics and optional alert thresholds."""

from __future__ import annotations

import argparse
import json
import statistics
from datetime import datetime, timedelta, timezone
from pathlib import Path
from typing import Any
import sys

if __package__ in (None, ""):
    sys.path.append(str(Path(__file__).resolve().parents[2]))

from tools.infra.injection_common import LANES, injections_root, repo_root


def parse_iso(ts: str) -> datetime | None:
    try:
        return datetime.fromisoformat(ts.replace("Z", "+00:00"))
    except Exception:
        return None


def pct(values: list[float], q: float) -> float:
    if not values:
        return 0.0
    if len(values) == 1:
        return values[0]
    k = (len(values) - 1) * q
    f = int(k)
    c = min(f + 1, len(values) - 1)
    if f == c:
        return values[f]
    return values[f] + (values[c] - values[f]) * (k - f)


def load_json_lines(path: Path) -> list[dict[str, Any]]:
    if not path.exists():
        return []
    rows: list[dict[str, Any]] = []
    for line in path.read_text(encoding="utf-8").splitlines():
        line = line.strip()
        if not line:
            continue
        try:
            row = json.loads(line)
        except json.JSONDecodeError:
            continue
        if isinstance(row, dict):
            rows.append(row)
    return rows


def packet_history_latency(packet: dict[str, Any]) -> float | None:
    hist = packet.get("history", [])
    if not isinstance(hist, list):
        return None
    created_at: datetime | None = None
    accepted_at: datetime | None = None
    for row in hist:
        if not isinstance(row, dict):
            continue
        event = str(row.get("event", ""))
        at = parse_iso(str(row.get("at", "")))
        if at is None:
            continue
        if event.startswith("created"):
            if created_at is None or at < created_at:
                created_at = at
        if event == "promoted:gated->accepted":
            if accepted_at is None or at > accepted_at:
                accepted_at = at
    if created_at and accepted_at and accepted_at >= created_at:
        return (accepted_at - created_at).total_seconds()
    return None


def main() -> int:
    parser = argparse.ArgumentParser(description="Build SLO report for injection pipeline")
    parser.add_argument("--since-hours", type=float, default=24.0, help="Time window for event metrics")
    parser.add_argument("--json-out", default="reports/injections/slo_metrics.json")
    parser.add_argument("--md-out", default="reports/injections/slo_metrics.md")
    parser.add_argument("--max-failure-rate", type=float, default=None)
    parser.add_argument("--max-p95-latency-sec", type=float, default=None)
    parser.add_argument("--max-p95-lock-wait-sec", type=float, default=None)
    parser.add_argument("--min-gpu-free-mb", type=float, default=None)
    args = parser.parse_args()

    root = repo_root()
    injections = injections_root(root)
    now = datetime.now(timezone.utc)
    since_dt = now - timedelta(hours=max(0.0, args.since_hours))

    lane_counts: dict[str, int] = {}
    accepted_packets: list[dict[str, Any]] = []
    rejected_count = 0
    for lane in LANES:
        lane_dir = injections / lane
        files = sorted(lane_dir.glob("*.json")) if lane_dir.exists() else []
        lane_counts[lane] = len(files)
        for path in files:
            try:
                packet = json.loads(path.read_text(encoding="utf-8"))
            except json.JSONDecodeError:
                continue
            if lane == "accepted":
                accepted_packets.append(packet)
            elif lane == "rejected":
                rejected_count += 1

    loop_latencies = sorted(
        x for x in (packet_history_latency(p) for p in accepted_packets) if x is not None
    )
    p50_latency = pct(loop_latencies, 0.5)
    p95_latency = pct(loop_latencies, 0.95)

    events_path = injections / "manifests" / "events.jsonl"
    events = load_json_lines(events_path)
    window_events: list[dict[str, Any]] = []
    for row in events:
        at = parse_iso(str(row.get("at", "")))
        if at is None:
            continue
        if at >= since_dt:
            window_events.append(row)

    lock_waits = sorted(
        float(row.get("extra", {}).get("lock_wait_sec", 0.0))
        for row in window_events
        if isinstance(row.get("extra"), dict)
    )
    p50_lock_wait = pct(lock_waits, 0.5)
    p95_lock_wait = pct(lock_waits, 0.95)

    gpu_total_free_mb: list[float] = []
    gpu_min_free_mb: list[float] = []
    for row in window_events:
        gpu = row.get("gpu", {})
        if not isinstance(gpu, dict) or not gpu.get("available"):
            continue
        gpus = gpu.get("gpus", [])
        if not isinstance(gpus, list) or not gpus:
            continue
        frees = [float(g.get("memory_free_mb", 0.0)) for g in gpus if isinstance(g, dict)]
        if not frees:
            continue
        gpu_total_free_mb.append(sum(frees))
        gpu_min_free_mb.append(min(frees))

    failure_den = lane_counts.get("accepted", 0) + rejected_count
    failure_rate = (rejected_count / failure_den) if failure_den > 0 else 0.0

    report = {
        "window": {"since_hours": args.since_hours, "events": len(window_events)},
        "lane_counts": lane_counts,
        "loop_latency_sec": {
            "sample_count": len(loop_latencies),
            "p50": p50_latency,
            "p95": p95_latency,
            "mean": statistics.fmean(loop_latencies) if loop_latencies else 0.0,
        },
        "failure_rate": failure_rate,
        "lock_wait_sec": {
            "sample_count": len(lock_waits),
            "p50": p50_lock_wait,
            "p95": p95_lock_wait,
            "mean": statistics.fmean(lock_waits) if lock_waits else 0.0,
        },
        "gpu_memory_mb": {
            "sample_count": len(gpu_total_free_mb),
            "p50_total_free": pct(sorted(gpu_total_free_mb), 0.5),
            "p95_total_free": pct(sorted(gpu_total_free_mb), 0.95),
            "min_free_across_gpus": min(gpu_min_free_mb) if gpu_min_free_mb else 0.0,
        },
    }

    json_out = root / args.json_out
    json_out.parent.mkdir(parents=True, exist_ok=True)
    json_out.write_text(json.dumps(report, ensure_ascii=True, indent=2) + "\n", encoding="utf-8")

    md_out = root / args.md_out
    md = f"""# Injection SLO Metrics

- Window (hours): `{args.since_hours}`
- Window events: `{report['window']['events']}`

## Loop Latency (sec)
- samples: `{report['loop_latency_sec']['sample_count']}`
- p50: `{report['loop_latency_sec']['p50']:.3f}`
- p95: `{report['loop_latency_sec']['p95']:.3f}`
- mean: `{report['loop_latency_sec']['mean']:.3f}`

## Failure
- rejected/(accepted+rejected): `{report['failure_rate']:.6f}`

## Lock Wait (sec)
- samples: `{report['lock_wait_sec']['sample_count']}`
- p50: `{report['lock_wait_sec']['p50']:.6f}`
- p95: `{report['lock_wait_sec']['p95']:.6f}`
- mean: `{report['lock_wait_sec']['mean']:.6f}`

## GPU Memory (MB)
- samples: `{report['gpu_memory_mb']['sample_count']}`
- p50 total free: `{report['gpu_memory_mb']['p50_total_free']:.2f}`
- p95 total free: `{report['gpu_memory_mb']['p95_total_free']:.2f}`
- min free across GPUs: `{report['gpu_memory_mb']['min_free_across_gpus']:.2f}`
"""
    md_out.parent.mkdir(parents=True, exist_ok=True)
    md_out.write_text(md, encoding="utf-8")

    violations: list[str] = []
    if args.max_failure_rate is not None and report["failure_rate"] > args.max_failure_rate:
        violations.append(
            f"failure_rate {report['failure_rate']:.6f} > max {args.max_failure_rate:.6f}"
        )
    if args.max_p95_latency_sec is not None and p95_latency > args.max_p95_latency_sec:
        violations.append(f"p95_latency_sec {p95_latency:.3f} > max {args.max_p95_latency_sec:.3f}")
    if args.max_p95_lock_wait_sec is not None and p95_lock_wait > args.max_p95_lock_wait_sec:
        violations.append(
            f"p95_lock_wait_sec {p95_lock_wait:.6f} > max {args.max_p95_lock_wait_sec:.6f}"
        )
    if args.min_gpu_free_mb is not None:
        min_free = report["gpu_memory_mb"]["min_free_across_gpus"]
        if min_free < args.min_gpu_free_mb:
            violations.append(f"min_gpu_free_mb {min_free:.2f} < required {args.min_gpu_free_mb:.2f}")

    print(json_out)
    print(md_out)
    if violations:
        for v in violations:
            print(f"SLO VIOLATION: {v}")
        return 2
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
