#!/usr/bin/env python3
"""Convert heartbeat log pulses into Hive QI packets, lineage edges, and routed tasks."""
from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import subprocess
from collections import Counter
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

try:
    from tools.infra import hive_arango_queue as queue
except ImportError:  # pragma: no cover
    import hive_arango_queue as queue


@dataclass
class Pulse:
    ts: str
    fields: dict[str, str]


def utc_now() -> str:
    return datetime.now(timezone.utc).replace(microsecond=0).isoformat().replace("+00:00", "Z")


def sha(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


def parse_heartbeat_log(path: Path) -> list[Pulse]:
    if not path.exists():
        return []
    lines = path.read_text(encoding="utf-8").splitlines()
    pulses: list[Pulse] = []
    current_ts = ""
    fields: dict[str, str] = {}
    for line in lines:
        if line.startswith("## heartbeat "):
            if current_ts:
                pulses.append(Pulse(ts=current_ts, fields=fields))
            current_ts = line.replace("## heartbeat", "").strip()
            fields = {}
            continue
        if not current_ts:
            continue
        if ":" in line:
            k, v = line.split(":", 1)
            fields[k.strip()] = v.strip()
    if current_ts:
        pulses.append(Pulse(ts=current_ts, fields=fields))
    return pulses


def parse_build_log_path(report_path: Path) -> Path | None:
    if not report_path.exists():
        return None
    for line in report_path.read_text(encoding="utf-8", errors="ignore").splitlines():
        if line.strip().startswith("- build_log:"):
            candidate = line.split(":", 1)[1].strip()
            if candidate:
                return Path(candidate)
    return None


def infer_declaration_name(file_path: Path, line_number: int) -> str:
    try:
        lines = file_path.read_text(encoding="utf-8", errors="ignore").splitlines()
    except OSError:
        return "unknown"
    upto = min(max(line_number, 1), len(lines))
    decl = "unknown"
    for i in range(upto):
        txt = lines[i].strip()
        if txt.startswith(("theorem ", "lemma ", "def ", "example ")):
            head = txt.split(":", 1)[0]
            parts = head.split()
            if len(parts) >= 2:
                decl = parts[1]
    return decl


def parse_sorry_obligations_from_build_log(
    build_log: Path,
    *,
    repo_root: Path,
    pulse_id: str,
    lane: str,
) -> list[dict[str, Any]]:
    if not build_log.exists():
        return []
    obligations: list[dict[str, Any]] = []
    pattern = re.compile(r"^error:\s+([^:]+\.lean):(\d+):(\d+):\s+(.*)$")
    for raw in build_log.read_text(encoding="utf-8", errors="ignore").splitlines():
        m = pattern.match(raw.strip())
        if not m:
            continue
        file_rel = m.group(1)
        line_no = int(m.group(2))
        col_no = int(m.group(3))
        message = m.group(4).strip()
        if file_rel.startswith("Lean exited") or file_rel.startswith("build failed"):
            continue
        file_abs = repo_root / file_rel
        declaration = infer_declaration_name(file_abs, line_no)
        sector = classify_geometric_sector(f"{file_rel} {message}")
        identity = f"{file_rel}:{line_no}:{declaration}:{message}"
        obligation_hash = sha(identity)[:24]
        obligations.append(
            {
                "_key": queue.stable_key("sob", obligation_hash),
                "schema": "info_geometry.hive_sorry_obligation.v1",
                "obligation_hash": obligation_hash,
                "pulse_id": pulse_id,
                "file": file_rel,
                "line": line_no,
                "column": col_no,
                "declaration": declaration,
                "message": message,
                "sector": sector,
                "lane": lane,
                "status": "present",
                "source": str(build_log),
                "updated_at": utc_now(),
            }
        )
    return obligations


def classify_blocker(summary: str) -> str:
    s = (summary or "").lower()
    if "unknown identifier" in s or "unknown constant" in s:
        return "missing_identifier"
    if "unsolved goals" in s:
        return "unsolved_goals"
    if "failed to synthesize" in s:
        return "typeclass"
    if "timeout" in s or "hang" in s:
        return "timeout"
    if "lock" in s:
        return "lock"
    if "syntax" in s or "parse" in s:
        return "syntax"
    return "unknown"


def parse_module_path(summary: str) -> str:
    if not summary:
        return "unknown"
    m = re.search(r"([A-Za-z0-9_/.-]+\.lean)", summary)
    if m:
        return m.group(1)
    return "unknown"


def infer_geometric_sector(summary: str, module_path: str) -> str:
    s = f"{summary} {module_path}".lower()
    if any(k in s for k in ["phase", "cauchy", "analytic"]):
        return "phase_geometry"
    if any(k in s for k in ["super", "susy", "fermion", "boson"]):
        return "supersymmetry"
    if any(k in s for k in ["krein", "indefinite", "modular", "kms"]):
        return "krein_metric"
    return "unknown"


def classify_geometric_sector(summary: str) -> str:
    s = (summary or "").lower()
    if any(k in s for k in ["phase", "clock", "hestenes", "linear", "anticommute", " j ", " k ", "epsilon"]):
        return "phase_geometry"
    if any(k in s for k in ["super", "fock", "parity", "graded", "bracket", " bose ", " fermi "]):
        return "supersymmetry"
    if "krein" in s or "inner" in s:
        return "krein_metric"
    return "generic_algebra"


def to_pulse_record(
    p: Pulse,
    *,
    source: str,
    entity_key: str,
    lineage_parent: str | None,
    repeated_blocker_streak: int,
    resolution_of: str | None,
    deadend_of: str | None,
) -> dict[str, Any]:
    summary = p.fields.get("build_summary", "")
    build_exit = p.fields.get("build_exit", "")
    sc_before = p.fields.get("sorry_count_before", p.fields.get("sorry_count", "0"))
    sc_after = p.fields.get("sorry_count_after", p.fields.get("sorry_count", "0"))
    error_fp = sha(summary)[:24] if summary else "none"
    blocker_kind = classify_blocker(summary)
    module_path = parse_module_path(summary)
    geometric_sector = infer_geometric_sector(summary, module_path)

    lane_affinity = "proof.search"
    if blocker_kind in {"timeout", "lock"} or deadend_of:
        lane_affinity = "build.verify"
    if repeated_blocker_streak >= 3:
        lane_affinity = "research.digest"

    severity = "high" if str(build_exit) == "1" else "low"
    pulse_id = f"pulse_{sha(p.ts)[:24]}"

    packet = {
        "schema": "info_geometry.hive_qi_heartbeat_pulse.v2",
        "meta": {
            "timestamp": p.fields.get("time", ""),
            "pulse_id": pulse_id,
            "lineage_parent": lineage_parent or "",
        },
        "telemetry": {
            "sorry_count_before": sc_before,
            "sorry_count_after": sc_after,
            "build_exit": build_exit,
            "elapsed_ms": p.fields.get("build_elapsed", ""),
            "touched_file": p.fields.get("edit_target", "none"),
        },
        "classification": {
            "blocker_kind": blocker_kind,
            "module_path": module_path,
            "error_fingerprint": error_fp,
            "severity": severity,
            "interdependence_anchor": module_path,
            "spectral_mode_hint": "dissipation" if blocker_kind in {"timeout", "lock"} else "coupling",
            "geometric_sector": geometric_sector,
        },
        "intent": {
            "next_action_hint": "fix_current_blocker_then_rebuild" if str(build_exit) == "1" else "advance_next_priority_module",
            "lane_affinity": lane_affinity,
        },
        "persistence": {
            "repeated_blocker_streak": repeated_blocker_streak,
            "deadend_of": deadend_of or "",
            "resolution_of": resolution_of or "",
        },
        "report": p.fields.get("report", ""),
        "build_summary": summary,
        "heartbeat": p.ts,
        "time": p.fields.get("time", ""),
    }
    packet_sha = sha(json.dumps(packet, sort_keys=True, ensure_ascii=False))
    return {
        "packet_sha256": packet_sha,
        "artifact_kind": "HeartbeatPulsePacket",
        "space": "hive_qi",
        "entity_key": entity_key,
        "canonical_shape": f"heartbeat:{p.ts}",
        "shape_sha256": sha(f"heartbeat:{p.ts}"),
        "source": source,
        "line_number": 0,
        "packet_index": 0,
        "packet": packet,
    }


def build_summary_record(records: list[dict[str, Any]], *, source: str, entity_key: str, window: int) -> dict[str, Any]:
    window_records = records[-window:] if records else []
    blocker_counts = Counter(
        r["packet"].get("classification", {}).get("blocker_kind", "unknown") for r in window_records
    )
    top3 = blocker_counts.most_common(3)
    build_failures = sum(1 for r in window_records if str(r["packet"].get("telemetry", {}).get("build_exit")) == "1")

    latest_packet = window_records[-1]["packet"] if window_records else {}
    streak = int(latest_packet.get("persistence", {}).get("repeated_blocker_streak", 0) or 0)

    sorry_before = [int(r["packet"].get("telemetry", {}).get("sorry_count_before", "0") or "0") for r in window_records]
    sorry_after = [int(r["packet"].get("telemetry", {}).get("sorry_count_after", "0") or "0") for r in window_records]
    velocity = 0.0
    if sorry_before and sorry_after:
        velocity = (sorry_before[0] - sorry_after[-1]) / max(1, len(window_records))

    stability = 0.0
    if window_records:
        successes = sum(1 for r in window_records if str(r["packet"].get("telemetry", {}).get("build_exit")) == "0")
        stability = successes / len(window_records)

    queue_directive = "normal"
    mix = {"proof.search": 0.70, "build.verify": 0.20, "research.digest": 0.10}
    if streak >= 3:
        queue_directive = "escalate_research"
        mix = {"proof.search": 0.30, "build.verify": 0.20, "research.digest": 0.50}
    elif stability < 0.5:
        queue_directive = "escalate_verify"
        mix = {"proof.search": 0.20, "build.verify": 0.70, "research.digest": 0.10}

    packet = {
        "schema": "info_geometry.hive_qi_motherbee_summary.v2",
        "epoch": utc_now(),
        "generated_at": utc_now(),
        "window": window,
        "sampled_pulses": len(window_records),
        "build_failures": build_failures,
        "top_blockers": [
            {
                "kind": k,
                "count": c,
                "hash": sha(k)[:16],
            }
            for k, c in top3
        ],
        "aggregate_stats": {
            "velocity": round(velocity, 3),
            "stability": round(stability, 3),
            "repeated_blocker_streak": streak,
        },
        "queue_mix_hint": mix,
        "queue_directive": queue_directive,
    }
    packet_sha = sha(json.dumps(packet, sort_keys=True, ensure_ascii=False))
    canonical = f"motherbee-summary:{packet['generated_at']}"
    return {
        "packet_sha256": packet_sha,
        "artifact_kind": "MotherBeeSummaryPacket",
        "space": "hive_qi",
        "entity_key": entity_key,
        "canonical_shape": canonical,
        "shape_sha256": sha(canonical),
        "source": source,
        "line_number": 0,
        "packet_index": 0,
        "packet": packet,
    }


def load_identity_packets(path: Path) -> list[dict[str, Any]]:
    if not path.exists():
        return []
    text = path.read_text(encoding="utf-8")
    data = json.loads(text)
    rows: list[dict[str, Any]] = []

    if isinstance(data, dict):
        candidate_packets = [data]
    elif isinstance(data, list):
        candidate_packets = [item for item in data if isinstance(item, dict)]
    else:
        candidate_packets = []

    for packet in candidate_packets:
        row = dict(packet)
        packet_id = str(row.get("packet_id") or sha(json.dumps(row, sort_keys=True, ensure_ascii=False))[:24])
        row.setdefault("_key", queue.stable_key("mip", packet_id))
        row.setdefault("schema", "hive.packet.majorana_identity.v1")
        row.setdefault("created_at", utc_now())
        rows.append(row)
    return rows


def load_identity_packets_from_run_dir(run_dir: Path) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    if not run_dir.exists():
        return rows
    for packet_file in sorted(run_dir.glob("*.packet.json")):
        rows.extend(load_identity_packets(packet_file))
    return rows


def invoke_identity_runner(*, repo_root: Path, fixtures: str, out_dir: str) -> tuple[bool, str, str]:
    cmd = [
        "python3",
        "tools/infra/identity_protocol_runner.py",
        "--stress-suite",
        fixtures,
        "--out-root",
        out_dir,
    ]
    proc = subprocess.run(cmd, cwd=str(repo_root), capture_output=True, text=True, check=False)
    ok = proc.returncode == 0
    return ok, proc.stdout.strip(), proc.stderr.strip()


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--log", default="artifacts/hermes_loop/heartbeat/hive_qi_heartbeat.log")
    ap.add_argument("--entity-key", default="fusion-sorry-heartbeat")
    ap.add_argument("--source", default="local_heartbeat")
    ap.add_argument("--window", type=int, default=10)
    ap.add_argument("--emit-summary", action="store_true")
    ap.add_argument("--print-json", action="store_true")
    ap.add_argument("--dry-run", action="store_true")
    ap.add_argument("--endpoint", default=os.getenv("ARANGO_ENDPOINT", "http://127.0.0.1:8530"))
    ap.add_argument("--database", default=os.getenv("ARANGO_DATABASE", "hive_live"))
    ap.add_argument("--username", default=os.getenv("ARANGO_USER") or os.getenv("ARANGO_USERNAME", "root"))
    ap.add_argument("--password", default=os.getenv("ARANGO_PASS") or os.getenv("ARANGO_PASSWORD", ""))
    ap.add_argument("--identity-packets-json", default="")
    ap.add_argument("--run-identity-protocol", action="store_true")
    ap.add_argument("--identity-fixtures", default="configs/identity_protocol/stress_suite.v1.jsonl")
    ap.add_argument("--identity-out-dir", default="artifacts/identity_protocol/runs")
    args = ap.parse_args()

    pulses = parse_heartbeat_log(Path(args.log))
    pulse_records: list[dict[str, Any]] = []

    previous_pulse_id: str | None = None
    previous_fp: str = "none"
    current_streak: int = 0
    pulse_fields_by_id: dict[str, dict[str, str]] = {}

    for pulse in pulses:
        summary = pulse.fields.get("build_summary", "")
        error_fp = sha(summary)[:24] if summary else "none"

        deadend_of: str | None = None
        resolution_of: str | None = None

        if error_fp != "none":
            if error_fp == previous_fp:
                current_streak += 1
                deadend_of = previous_pulse_id
            else:
                current_streak = 1
        else:
            if previous_fp != "none":
                resolution_of = previous_pulse_id
            current_streak = 0

        rec = to_pulse_record(
            pulse,
            source=args.source,
            entity_key=args.entity_key,
            lineage_parent=previous_pulse_id,
            repeated_blocker_streak=current_streak,
            resolution_of=resolution_of,
            deadend_of=deadend_of,
        )
        pulse_records.append(rec)
        pulse_id = rec["packet"]["meta"]["pulse_id"]
        pulse_fields_by_id[pulse_id] = dict(pulse.fields)
        previous_pulse_id = pulse_id
        previous_fp = error_fp

    summary_record = build_summary_record(pulse_records, source=args.source, entity_key=args.entity_key, window=args.window) if args.emit_summary else None
    all_records = pulse_records + ([summary_record] if summary_record else [])

    events = [queue.build_event_doc(r) for r in all_records]
    pulse_events = [ev for ev in events if ev.get("artifact_kind") == "HeartbeatPulsePacket"]
    summary_events = [ev for ev in events if ev.get("artifact_kind") == "MotherBeeSummaryPacket"]

    event_by_pulse_id = {ev["packet"]["meta"]["pulse_id"]: ev for ev in pulse_events}

    succession_edges: list[dict[str, Any]] = []
    resolution_edges: list[dict[str, Any]] = []
    deadend_edges: list[dict[str, Any]] = []
    pulse_to_blocker_edges: list[dict[str, Any]] = []
    blocker_to_task_edges: list[dict[str, Any]] = []
    interdependence_edges: list[dict[str, Any]] = []
    spectral_mode_edges: list[dict[str, Any]] = []
    blocker_modules: list[dict[str, Any]] = []
    negative_constraints: list[dict[str, Any]] = []
    sorry_obligations: list[dict[str, Any]] = []
    pulse_to_obligation_edges: list[dict[str, Any]] = []
    obligation_resolved_by_edges: list[dict[str, Any]] = []

    triggered_tasks: list[dict[str, Any]] = []
    repo_root = Path(__file__).resolve().parents[2]
    previous_obligation_keys: set[str] | None = None

    for ev in pulse_events:
        p = ev["packet"]
        pulse_id = p["meta"]["pulse_id"]
        parent_id = p["meta"].get("lineage_parent") or ""
        persistence = p.get("persistence", {})
        deadend_of = persistence.get("deadend_of") or ""
        resolution_of = persistence.get("resolution_of") or ""

        blocker_kind = p.get("classification", {}).get("blocker_kind", "unknown")
        module_path = p.get("classification", {}).get("module_path", "unknown")
        blocker_hash = p.get("classification", {}).get("error_fingerprint", "none")
        geometric_sector = p.get("classification", {}).get("geometric_sector", "unknown")

        if parent_id and parent_id in event_by_pulse_id:
            parent_key = event_by_pulse_id[parent_id]["_key"]
            succession_edges.append(
                {
                    "_key": queue.stable_key("succession", parent_id, pulse_id),
                    "_from": f"hive_events/{parent_key}",
                    "_to": f"hive_events/{ev['_key']}",
                    "schema": "info_geometry.hive_pulse_succession.v1",
                    "created_at": utc_now(),
                }
            )

        if deadend_of and deadend_of in event_by_pulse_id:
            from_key = event_by_pulse_id[deadend_of]["_key"]
            deadend_edges.append(
                {
                    "_key": queue.stable_key("deadend", deadend_of, pulse_id),
                    "_from": f"hive_events/{from_key}",
                    "_to": f"hive_events/{ev['_key']}",
                    "schema": "info_geometry.hive_pulse_deadend.v1",
                    "created_at": utc_now(),
                }
            )
            negative_constraints.append(
                {
                    "_key": queue.stable_key("negative", deadend_of, pulse_id, blocker_hash),
                    "schema": "info_geometry.hive_negative_constraint.v1",
                    "from_pulse_id": deadend_of,
                    "to_pulse_id": pulse_id,
                    "error_fingerprint": blocker_hash,
                    "blocker_kind": blocker_kind,
                    "module_path": module_path,
                    "geometric_sector": geometric_sector,
                    "severity": p.get("classification", {}).get("severity", "low"),
                    "build_summary": p.get("build_summary", ""),
                    "report": p.get("report", ""),
                    "created_at": utc_now(),
                }
            )

        if resolution_of and resolution_of in event_by_pulse_id:
            from_key = event_by_pulse_id[resolution_of]["_key"]
            resolution_edges.append(
                {
                    "_key": queue.stable_key("resolution", resolution_of, pulse_id),
                    "_from": f"hive_events/{from_key}",
                    "_to": f"hive_events/{ev['_key']}",
                    "schema": "info_geometry.hive_pulse_resolution.v1",
                    "created_at": utc_now(),
                }
            )

        blocker_key = queue.stable_key("qiblocker", blocker_hash, blocker_kind, module_path)
        blocker_modules.append(
            {
                "_key": blocker_key,
                "schema": "info_geometry.hive_qi_blocker_module.v1",
                "blocker_hash": blocker_hash,
                "blocker_kind": blocker_kind,
                "module_path": module_path,
                "severity": p.get("classification", {}).get("severity", "low"),
                "updated_at": utc_now(),
            }
        )
        pulse_to_blocker_edges.append(
            {
                "_key": queue.stable_key("p2b", pulse_id, blocker_key),
                "_from": f"hive_qi_pulses/{ev['_key']}",
                "_to": f"hive_qi_blocker_modules/{blocker_key}",
                "schema": "info_geometry.hive_qi_pulse_to_blocker.v1",
                "created_at": utc_now(),
            }
        )

        interdependence_edges.append(
            {
                "_key": queue.stable_key("indranet", pulse_id, blocker_key),
                "_from": f"hive_qi_pulses/{ev['_key']}",
                "_to": f"hive_qi_blocker_modules/{blocker_key}",
                "schema": "info_geometry.hive_interdependence_edge.v1",
                "edge_type": "InterdependenceEdge",
                "anchor": p.get("classification", {}).get("interdependence_anchor", "unknown"),
                "created_at": utc_now(),
            }
        )

        spectral_mode_edges.append(
            {
                "_key": queue.stable_key("spectral", pulse_id, blocker_key),
                "_from": f"hive_qi_pulses/{ev['_key']}",
                "_to": f"hive_qi_blocker_modules/{blocker_key}",
                "schema": "info_geometry.hive_spectral_mode_edge.v1",
                "edge_type": "SpectralModeEdge",
                "mode_hint": p.get("classification", {}).get("spectral_mode_hint", "coupling"),
                "created_at": utc_now(),
            }
        )

        fields = pulse_fields_by_id.get(pulse_id, {})
        report_path = Path(fields.get("report", "")) if fields.get("report") else None
        current_keys: set[str] = set()
        has_obligation_snapshot = False
        if report_path is not None:
            build_log = parse_build_log_path(report_path)
            if build_log is not None and build_log.exists():
                parsed = parse_sorry_obligations_from_build_log(
                    build_log,
                    repo_root=repo_root,
                    pulse_id=pulse_id,
                    lane=p.get("intent", {}).get("lane_affinity", "proof.search"),
                )
                has_obligation_snapshot = True
                for ob in parsed:
                    key = ob["_key"]
                    if key in current_keys:
                        continue
                    current_keys.add(key)
                    sorry_obligations.append(ob)
                    pulse_to_obligation_edges.append(
                        {
                            "_key": queue.stable_key("p2o", pulse_id, key),
                            "_from": f"hive_qi_pulses/{ev['_key']}",
                            "_to": f"hive_sorry_obligations/{key}",
                            "schema": "info_geometry.hive_qi_pulse_to_obligation.v1",
                            "created_at": utc_now(),
                        }
                    )

        if has_obligation_snapshot and previous_obligation_keys is not None:
            resolved = previous_obligation_keys - current_keys
            for ob_key in sorted(resolved):
                obligation_resolved_by_edges.append(
                    {
                        "_key": queue.stable_key("o2r", ob_key, pulse_id),
                        "_from": f"hive_sorry_obligations/{ob_key}",
                        "_to": f"hive_qi_pulses/{ev['_key']}",
                        "schema": "info_geometry.hive_qi_obligation_resolved_by.v1",
                        "created_at": utc_now(),
                    }
                )
            previous_obligation_keys = current_keys
        elif has_obligation_snapshot:
            previous_obligation_keys = current_keys

    if summary_record is not None and pulse_events:
        summary_packet = summary_record["packet"]
        directive = summary_packet.get("queue_directive", "normal")
        latest_pulse = pulse_events[-1]
        latest_packet = latest_pulse["packet"]
        touched = latest_packet.get("telemetry", {}).get("touched_file", "none")
        latest_blocker_hash = latest_packet.get("classification", {}).get("error_fingerprint", "none")
        latest_blocker_kind = latest_packet.get("classification", {}).get("blocker_kind", "unknown")
        latest_module_path = latest_packet.get("classification", {}).get("module_path", "unknown")
        latest_geometric_sector = latest_packet.get("classification", {}).get("geometric_sector", "unknown")
        blocker_key = queue.stable_key("qiblocker", latest_blocker_hash, latest_blocker_kind, latest_module_path)

        if directive == "escalate_verify" and touched and touched != "none":
            task = queue.enqueue_build_verify_task(
                args.endpoint,
                args.database,
                args.username,
                args.password,
                queue_name="build-verify",
                verification_key=f"qi_{latest_pulse['_key']}",
                target=touched,
                priority=0.9,
            )
            triggered_tasks.append({"kind": "build.verify", "task": task.get("task", {})})
            if task.get("task"):
                blocker_to_task_edges.append(
                    {
                        "_key": queue.stable_key("b2t", blocker_key, task["task"]["_key"]),
                        "_from": f"hive_qi_blocker_modules/{blocker_key}",
                        "_to": f"hive_tasks/{task['task']['_key']}",
                        "schema": "info_geometry.hive_qi_blocker_to_task.v1",
                        "suggestion": "build.verify",
                        "created_at": utc_now(),
                    }
                )

        if directive == "escalate_research":
            task = queue.enqueue_research_digest_task(
                args.endpoint,
                args.database,
                args.username,
                args.password,
                queue_name="research-digest",
                source_key=latest_pulse["_key"],
                summary_key=summary_events[-1]["_key"] if summary_events else "none",
                context=json.dumps(
                    {
                        "blocker_kind": latest_blocker_kind,
                        "module_path": latest_module_path,
                        "error_fingerprint": latest_blocker_hash,
                        "geometric_sector": latest_geometric_sector,
                        "summary": latest_packet.get("build_summary", ""),
                    },
                    ensure_ascii=False,
                ),
                priority=0.85,
            )
            triggered_tasks.append({"kind": "research.digest", "task": task.get("task", {})})
            if task.get("task"):
                blocker_to_task_edges.append(
                    {
                        "_key": queue.stable_key("b2t", blocker_key, task["task"]["_key"]),
                        "_from": f"hive_qi_blocker_modules/{blocker_key}",
                        "_to": f"hive_tasks/{task['task']['_key']}",
                        "schema": "info_geometry.hive_qi_blocker_to_task.v1",
                        "suggestion": "research.digest",
                        "created_at": utc_now(),
                    }
                )

    identity_packets: list[dict[str, Any]] = []
    identity_runner_status: dict[str, Any] = {"enabled": bool(args.run_identity_protocol), "ok": None}
    if args.run_identity_protocol:
        try:
            ok, stdout_text, stderr_text = invoke_identity_runner(
                repo_root=repo_root,
                fixtures=args.identity_fixtures,
                out_dir=args.identity_out_dir,
            )
            identity_runner_status.update({"ok": ok, "stdout": stdout_text[-5000:], "stderr": stderr_text[-2000:]})
            if ok:
                run_meta = json.loads(stdout_text) if stdout_text else {}
                out_dir = Path(str(run_meta.get("out_dir", "")))
                if out_dir:
                    identity_packets.extend(load_identity_packets_from_run_dir(out_dir))
        except Exception as exc:  # passive observer mode: never fail heartbeat
            identity_runner_status.update({"ok": False, "error": str(exc)})

    if args.identity_packets_json:
        identity_packets.extend(load_identity_packets(Path(args.identity_packets_json)))

    # Deduplicate by _key
    identity_packets = list({row.get("_key", queue.stable_key("mip", row.get("packet_id", "none"))): row for row in identity_packets}.values())

    result = {
        "parsed_pulses": len(pulses),
        "event_docs": len(events),
        "qi_pulses": len(pulse_events),
        "qi_summaries": len(summary_events),
        "identity_runner": identity_runner_status,
        "identity_packets": len(identity_packets),
        "edges": {
            "succession": len(succession_edges),
            "deadend": len(deadend_edges),
            "resolution": len(resolution_edges),
            "interdependence": len(interdependence_edges),
            "spectral_mode": len(spectral_mode_edges),
            "pulse_to_blocker": len(pulse_to_blocker_edges),
            "blocker_to_task": len(blocker_to_task_edges),
            "pulse_to_obligation": len(pulse_to_obligation_edges),
            "obligation_resolved_by": len(obligation_resolved_by_edges),
        },
        "negative_constraints": len(negative_constraints),
        "sorry_obligations": len({d.get('_key') for d in sorry_obligations}),
        "triggered_tasks": triggered_tasks,
        "latest_heartbeat": (pulses[-1].ts if pulses else None),
        "latest_build_exit": (pulses[-1].fields.get("build_exit") if pulses else None),
    }

    if args.dry_run:
        print(json.dumps({**result, "preview_events": events[-3:]}, ensure_ascii=False, indent=2))
        return

    queue.init_schema(args.endpoint, args.database, args.username, args.password)
    queue.import_rows(args.endpoint, args.database, args.username, args.password, "hive_events", events)
    queue.import_rows(args.endpoint, args.database, args.username, args.password, "hive_qi_pulses", pulse_events)
    queue.import_rows(args.endpoint, args.database, args.username, args.password, "hive_qi_summaries", summary_events)
    queue.import_rows(args.endpoint, args.database, args.username, args.password, "hive_qi_blocker_modules", blocker_modules)
    queue.import_rows(args.endpoint, args.database, args.username, args.password, "hive_negative_constraints", negative_constraints)
    queue.import_rows(
        args.endpoint,
        args.database,
        args.username,
        args.password,
        "hive_sorry_obligations",
        list({row["_key"]: row for row in sorry_obligations}.values()),
    )
    if identity_packets:
        queue.import_rows(args.endpoint, args.database, args.username, args.password, "hive_majorana_identity_packets", identity_packets)

    queue.import_rows(args.endpoint, args.database, args.username, args.password, "hive_pulse_succession", succession_edges)
    queue.import_rows(args.endpoint, args.database, args.username, args.password, "hive_pulse_deadend", deadend_edges)
    queue.import_rows(args.endpoint, args.database, args.username, args.password, "hive_pulse_resolution", resolution_edges)
    queue.import_rows(args.endpoint, args.database, args.username, args.password, "hive_interdependence_edges", interdependence_edges)
    queue.import_rows(args.endpoint, args.database, args.username, args.password, "hive_spectral_mode_edges", spectral_mode_edges)
    queue.import_rows(args.endpoint, args.database, args.username, args.password, "hive_qi_pulse_to_blocker", pulse_to_blocker_edges)
    queue.import_rows(args.endpoint, args.database, args.username, args.password, "hive_qi_blocker_to_task", blocker_to_task_edges)
    queue.import_rows(args.endpoint, args.database, args.username, args.password, "hive_qi_pulse_to_obligation", pulse_to_obligation_edges)
    queue.import_rows(args.endpoint, args.database, args.username, args.password, "hive_qi_obligation_resolved_by", obligation_resolved_by_edges)

    print(json.dumps(result, ensure_ascii=False, indent=2))


if __name__ == "__main__":
    main()
