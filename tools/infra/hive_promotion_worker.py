#!/usr/bin/env python3
"""PromotionBee worker for explicit Hive promotion decisions.

Promotion is intentionally separate from proof, build, and audit.  This worker
consumes `audit.semantic` outputs and emits `PromotionDecisionPacket` rows.  It
does not mutate Lean files and does not treat conditional audits as promotion.
"""

from __future__ import annotations

import argparse
import json
import sys
import time
from dataclasses import dataclass
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[2]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from tools.infra import hive_arango_queue as queue_tool

DEFAULT_HIVE_ENDPOINT = queue_tool.DEFAULT_ENDPOINT
DEFAULT_HIVE_DATABASE = queue_tool.DEFAULT_DATABASE
DEFAULT_HIVE_USERNAME = queue_tool.DEFAULT_USERNAME
DEFAULT_HIVE_PASSWORD = queue_tool.DEFAULT_PASSWORD
DEFAULT_QUEUE = "promotion-decide"
DEFAULT_WORKER_ID = "hive-promotionbee-001"
DEFAULT_LEASE_SECONDS = queue_tool.DEFAULT_LEASE_SECONDS


@dataclass(frozen=True)
class PromotionBeeConfig:
    hive_endpoint: str
    hive_database: str
    hive_username: str
    hive_password: str
    queue_name: str
    worker_id: str
    lease_seconds: int


def claim_promotion_task(config: PromotionBeeConfig) -> dict[str, Any] | None:
    queue_tool.init_schema(
        config.hive_endpoint,
        config.hive_database,
        config.hive_username,
        config.hive_password,
    )
    queue_tool.heartbeat_worker(
        config.hive_endpoint,
        config.hive_database,
        config.hive_username,
        config.hive_password,
        worker_id=config.worker_id,
        capabilities=["promotion-decision", "audit-gated-promotion"],
        queues=[config.queue_name],
    )
    return queue_tool.claim_next_task(
        config.hive_endpoint,
        config.hive_database,
        config.hive_username,
        config.hive_password,
        worker_id=config.worker_id,
        queue_name=config.queue_name,
        lease_seconds=config.lease_seconds,
        task_kind="promotion.decide",
    )


def fetch_audit_packet(config: PromotionBeeConfig, audit_key: str) -> dict[str, Any] | None:
    return queue_tool.fetch_packet_by_key(
        config.hive_endpoint,
        config.hive_database,
        config.hive_username,
        config.hive_password,
        schema="hive.packet.audit.v1",
        packet_key_value=audit_key,
    )


def decide_promotion(audit: dict[str, Any] | None, *, allow_override: bool) -> tuple[str, list[str]]:
    if not audit:
        return "reject", ["missing AuditPacket"]
    verdict = str(audit.get("verdict") or "")
    origin = str(audit.get("verification_origin") or "")
    promotion_allowed = bool(audit.get("promotion_allowed"))
    reasons: list[str] = []
    if verdict == "fail":
        return "reject", ["audit verdict is fail"]
    if verdict == "conditional_pass":
        reasons.append("audit verdict is conditional_pass")
    if origin == "synthetic_smoke":
        reasons.append("verification origin is synthetic_smoke")
    if not promotion_allowed:
        reasons.append("audit packet does not allow promotion")
    if verdict == "pass" and promotion_allowed and (origin != "synthetic_smoke" or allow_override):
        return "promote", ["audit pass and promotion_allowed accepted"]
    if allow_override and verdict == "pass":
        return "promote", ["explicit override accepted for audit pass"]
    return "hold", reasons or ["promotion held by conservative policy"]


def emit_promotion_packet(
    config: PromotionBeeConfig,
    task: dict[str, Any],
    *,
    audit: dict[str, Any],
    decision: str,
    reasons: list[str],
) -> dict[str, Any]:
    packet = {
        "schema": "hive.packet.promotion_decision.v1",
        "authority": "promoted",
        "representation_class": audit.get("representation_class") or "owner",
        "representation_depth": audit.get("representation_depth") or "operatorial",
        "source_regime": "synthetic_smoke" if audit.get("verification_origin") == "synthetic_smoke" else "theorem_lane",
        "promotion_origin": "promotionbee",
        "audit_key": audit["packet_key"],
        "decision": decision,
        "reasons": reasons,
        "audit_verdict": audit.get("verdict"),
        "verification_origin": audit.get("verification_origin"),
        "promotion_allowed_by_audit": bool(audit.get("promotion_allowed")),
        "worker_id": config.worker_id,
        "task_key": task.get("_key"),
    }
    return queue_tool.import_packet_with_lineage(
        config.hive_endpoint,
        config.hive_database,
        config.hive_username,
        config.hive_password,
        packet=packet,
        task_key_value=str(task.get("_key") or ""),
        dependencies=[audit],
    )["packet"]


def run_one(config: PromotionBeeConfig) -> dict[str, Any]:
    task = claim_promotion_task(config)
    if not task:
        return {"status": "idle", "worker_id": config.worker_id, "queue_name": config.queue_name}

    audit_key = str(task.get("audit_key") or "")
    audit = fetch_audit_packet(config, audit_key)
    decision, reasons = decide_promotion(audit, allow_override=bool(task.get("allow_override")))
    if not audit:
        updated_task = queue_tool.fail_task(
            config.hive_endpoint,
            config.hive_database,
            config.hive_username,
            config.hive_password,
            task_key_value=str(task["_key"]),
            worker_id=config.worker_id,
            error_message="promotion task references missing AuditPacket",
        )
        return {"status": "failed", "task": updated_task or task, "decision": decision, "reasons": reasons}

    promotion_packet = emit_promotion_packet(
        config,
        task,
        audit=audit,
        decision=decision,
        reasons=reasons,
    )
    updated_task = queue_tool.complete_task(
        config.hive_endpoint,
        config.hive_database,
        config.hive_username,
        config.hive_password,
        task_key_value=str(task["_key"]),
        worker_id=config.worker_id,
    )
    return {"status": decision, "task": updated_task or task, "promotion_packet": promotion_packet}


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--hive-endpoint", default=DEFAULT_HIVE_ENDPOINT)
    parser.add_argument("--hive-database", default=DEFAULT_HIVE_DATABASE)
    parser.add_argument("--hive-username", default=DEFAULT_HIVE_USERNAME)
    parser.add_argument("--hive-password", default=DEFAULT_HIVE_PASSWORD)
    parser.add_argument("--queue-name", default=DEFAULT_QUEUE)
    parser.add_argument("--worker-id", default=DEFAULT_WORKER_ID)
    parser.add_argument("--lease-seconds", type=int, default=DEFAULT_LEASE_SECONDS)
    parser.add_argument("--once", action="store_true", help="run one promotion task and exit")
    parser.add_argument("--poll-interval", type=int, default=15)
    return parser.parse_args()


def config_from_args(args: argparse.Namespace) -> PromotionBeeConfig:
    return PromotionBeeConfig(
        hive_endpoint=str(args.hive_endpoint).rstrip("/"),
        hive_database=str(args.hive_database),
        hive_username=str(args.hive_username),
        hive_password=str(args.hive_password),
        queue_name=str(args.queue_name),
        worker_id=str(args.worker_id),
        lease_seconds=int(args.lease_seconds),
    )


def main() -> int:
    args = parse_args()
    config = config_from_args(args)
    while True:
        result = run_one(config)
        print(json.dumps(result, indent=2, ensure_ascii=False, sort_keys=True))
        if args.once:
            return 0
        time.sleep(max(1, int(args.poll_interval)))


if __name__ == "__main__":
    raise SystemExit(main())
