#!/usr/bin/env python3
"""
tools/infra/identity_protocol_runner.py

Runs Identity Protocol fixtures and writes majorana identity packet artifacts.
Local-first: writes artifacts only; heartbeat/queue handles ingestion.
"""

from __future__ import annotations

import argparse
import datetime as dt
import hashlib
import json
import pathlib
import sys
import uuid
from typing import Any, Dict, Iterable, List

try:
    from tools.infra.identity_protocol_metrics import evaluate_identity_fixture
except ModuleNotFoundError:  # script execution from repo root
    from identity_protocol_metrics import evaluate_identity_fixture


ALLOWED_VERDICTS = {"UNIFIED", "CONDITIONAL", "BIFURCATED"}


def utc_now_iso() -> str:
    return dt.datetime.now(dt.timezone.utc).isoformat()


def sha256_json(obj: Any) -> str:
    payload = json.dumps(obj, sort_keys=True, separators=(",", ":")).encode("utf-8")
    return hashlib.sha256(payload).hexdigest()


def load_json(path: pathlib.Path) -> Dict[str, Any]:
    with path.open("r", encoding="utf-8") as f:
        return json.load(f)


def load_jsonl(path: pathlib.Path) -> Iterable[Dict[str, Any]]:
    with path.open("r", encoding="utf-8") as f:
        for line_no, line in enumerate(f, start=1):
            stripped = line.strip()
            if not stripped:
                continue
            try:
                yield json.loads(stripped)
            except json.JSONDecodeError as exc:
                raise ValueError(f"{path}:{line_no}: invalid JSONL record") from exc


def validate_fixture_expected_verdict(fixture: dict, result: dict) -> dict:
    fixture_id = fixture.get("fixture_id", "<missing-fixture-id>")
    expected = fixture.get("expected_verdict")
    actual = result.get("verdict")

    if expected is None:
        return {
            "ok": False,
            "fixture_id": fixture_id,
            "kind": "missing_expected_verdict",
            "expected": None,
            "actual": actual,
            "error": (
                f"Regressed Identity Symmetry: fixture={fixture_id} "
                f"expected=<missing> got={actual}"
            ),
        }

    if expected not in ALLOWED_VERDICTS:
        return {
            "ok": False,
            "fixture_id": fixture_id,
            "kind": "invalid_expected_verdict",
            "expected": expected,
            "actual": actual,
            "error": (
                f"Regressed Identity Symmetry: fixture={fixture_id} "
                f"expected={expected} is invalid"
            ),
        }

    if actual not in ALLOWED_VERDICTS:
        return {
            "ok": False,
            "fixture_id": fixture_id,
            "kind": "invalid_actual_verdict",
            "expected": expected,
            "actual": actual,
            "error": (
                f"Regressed Identity Symmetry: fixture={fixture_id} "
                f"actual={actual} is invalid"
            ),
        }

    if expected != actual:
        return {
            "ok": False,
            "fixture_id": fixture_id,
            "kind": "verdict_mismatch",
            "expected": expected,
            "actual": actual,
            "error": (
                f"Regressed Identity Symmetry: fixture={fixture_id} "
                f"expected={expected} got={actual}"
            ),
        }

    return {
        "ok": True,
        "fixture_id": fixture_id,
        "expected": expected,
        "actual": actual,
    }


def make_packet(*, run_id: str, episode_ix: int, fixture: Dict[str, Any], result: Dict[str, Any]) -> Dict[str, Any]:
    fixture_id = fixture.get("fixture_id")
    if not fixture_id:
        raise ValueError("fixture missing required field: fixture_id")

    episode_id = f"{run_id}:{fixture_id}:{episode_ix:04d}"
    packet_id = hashlib.sha256(episode_id.encode("utf-8")).hexdigest()[:24]

    state_a = fixture.get("state_a", {})
    state_b = fixture.get("state_b", {})

    packet = {
        "schema": "hive.packet.majorana_identity.v1",
        "schema_version": "hive.packet.majorana_identity.v1",
        "authority": "semantic",
        "packet_id": packet_id,
        "episode_id": episode_id,
        "run_id": run_id,
        "created_at": utc_now_iso(),
        "fixture_id": fixture_id,
        "fixture_family": fixture.get("fixture_family", "unknown"),
        "metric_mode": result.get("metric_mode", "proxy"),
        "metric_sources": result.get("metric_sources", {}),
        "state_ref": {
            "state_a_hash": sha256_json(state_a),
            "state_b_hash": sha256_json(state_b),
        },
        "inputs": {
            "fixture_hash": sha256_json(fixture),
            "prompt_hash": sha256_json(fixture.get("prompt", "")),
            "state_a_hash": sha256_json(state_a),
            "state_b_hash": sha256_json(state_b),
        },
        "metrics": result["metrics"],
        "fingerprints": result.get(
            "fingerprints",
            {
                "debruijn_hashes": [],
                "scc_basin_ids": [],
                "motif_hashes": [],
            },
        ),
        "gates": result["gates"],
        "verdict": result["verdict"],
        "blockers": result.get("blockers", []),
        "notes": result.get("notes", []),
    }
    return packet


def write_packet(out_dir: pathlib.Path, packet: Dict[str, Any]) -> pathlib.Path:
    out_dir.mkdir(parents=True, exist_ok=True)
    safe_fixture = packet["fixture_id"].replace("/", "_")
    safe_episode = packet["episode_id"].replace(":", "_")
    path = out_dir / f"{safe_fixture}.{safe_episode}.packet.json"
    with path.open("w", encoding="utf-8") as f:
        json.dump(packet, f, indent=2, sort_keys=True)
        f.write("\n")
    return path


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--thresholds", type=pathlib.Path, default=pathlib.Path("configs/identity_protocol/thresholds.v1.json"))
    parser.add_argument("--stress-suite", type=pathlib.Path, default=pathlib.Path("configs/identity_protocol/stress_suite.v1.jsonl"))
    parser.add_argument("--out-root", type=pathlib.Path, default=pathlib.Path("artifacts/identity_protocol/runs"))
    parser.add_argument("--episodes", type=int, default=3)
    parser.add_argument("--print-summary", action="store_true")
    parser.add_argument(
        "--no-strict-fixture-verdicts",
        action="store_true",
        help="Do not fail the run when fixture.expected_verdict differs from computed verdict.",
    )
    args = parser.parse_args()

    thresholds = load_json(args.thresholds)
    fixtures = list(load_jsonl(args.stress_suite))

    run_id = dt.datetime.now(dt.timezone.utc).strftime("%Y%m%dT%H%M%SZ") + "-" + uuid.uuid4().hex[:8]
    out_dir = args.out_root / run_id
    out_dir.mkdir(parents=True, exist_ok=True)

    verdict_checks = []
    packets: List[Dict[str, Any]] = []

    for i in range(max(0, args.episodes)):
        fixture = fixtures[i % len(fixtures)]
        result = evaluate_identity_fixture(fixture, thresholds)

        verdict_check = validate_fixture_expected_verdict(fixture, result)
        verdict_checks.append(verdict_check)

        packet = make_packet(run_id=run_id, episode_ix=i, fixture=fixture, result=result)
        write_packet(out_dir, packet)
        packets.append(packet)

    packets_path = out_dir / "identity_packets.json"
    with packets_path.open("w", encoding="utf-8") as f:
        json.dump(packets, f, indent=2, sort_keys=True)
        f.write("\n")

    mismatches = [c for c in verdict_checks if not c["ok"]]

    summary = {
        "schema_version": "identity_protocol.run_summary.v1",
        "run_id": run_id,
        "created_at": utc_now_iso(),
        "out_dir": str(out_dir),
        "packet_count": len(packets),
        "verdict_counts": {
            verdict: sum(1 for p in packets if p["verdict"] == verdict)
            for verdict in sorted({p["verdict"] for p in packets})
        },
        "fixture_verdict_validation": {
            "strict": not args.no_strict_fixture_verdicts,
            "ok": len(mismatches) == 0,
            "checks": verdict_checks,
            "mismatches": mismatches,
        },
    }

    with (out_dir / "summary.json").open("w", encoding="utf-8") as f:
        json.dump(summary, f, indent=2, sort_keys=True)
        f.write("\n")

    if args.print_summary:
        print(json.dumps(summary, indent=2, sort_keys=True))

    if mismatches and not args.no_strict_fixture_verdicts:
        for mismatch in mismatches:
            err = mismatch.get("error") or (
                f"Regressed Identity Symmetry: fixture={mismatch.get('fixture_id')} "
                f"expected={mismatch.get('expected')} got={mismatch.get('actual')}"
            )
            print(err, file=sys.stderr)
        return 2
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
