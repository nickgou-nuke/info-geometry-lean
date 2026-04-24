#!/usr/bin/env python3
"""AuditBee worker for first-class Hive audit.semantic tasks.

AuditBee is an authority gate, not a promotion worker.  It consumes a completed
BuildPacket, checks conservative semantic hygiene around the build result and
its verification anchor, emits an AuditPacket, and stops there.
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
DEFAULT_QUEUE = "audit-semantic"
DEFAULT_WORKER_ID = "hive-auditbee-001"
DEFAULT_LEASE_SECONDS = queue_tool.DEFAULT_LEASE_SECONDS


@dataclass(frozen=True)
class AuditBeeConfig:
    hive_endpoint: str
    hive_database: str
    hive_username: str
    hive_password: str
    queue_name: str
    worker_id: str
    lease_seconds: int


def claim_audit_task(config: AuditBeeConfig) -> dict[str, Any] | None:
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
        capabilities=["audit-semantic", "build-packet-audit"],
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
        task_kind="audit.semantic",
    )


def fetch_build_packet(config: AuditBeeConfig, build_key: str) -> dict[str, Any] | None:
    return queue_tool.fetch_packet_by_key(
        config.hive_endpoint,
        config.hive_database,
        config.hive_username,
        config.hive_password,
        schema="hive.packet.build.v1",
        packet_key_value=build_key,
    )


def fetch_verification_packet(config: AuditBeeConfig, verification_key: str) -> dict[str, Any] | None:
    return queue_tool.fetch_packet_by_key(
        config.hive_endpoint,
        config.hive_database,
        config.hive_username,
        config.hive_password,
        schema="hive.packet.verification.v1",
        packet_key_value=verification_key,
    )


def fetch_upstream_provenance(config: AuditBeeConfig, build_key: str) -> dict[str, Any]:
    lineage = queue_tool.lineage_upstream(
        config.hive_endpoint,
        config.hive_database,
        config.hive_username,
        config.hive_password,
        packet_key_value=build_key,
        schema="hive.packet.build.v1",
        depth=5,
    )
    provenance: dict[str, Any] = {"lineage_rows": lineage.get("rows") or []}
    for row in provenance["lineage_rows"]:
        vertex = row.get("vertex") or {}
        schema = vertex.get("schema")
        if schema == "hive.packet.proposal.v1":
            provenance.setdefault("proposal", vertex)
        elif schema == "hive.packet.execution_intent.v1":
            provenance.setdefault("execution_intent", vertex)
        elif schema == "hive.packet.critique.v1":
            provenance.setdefault("critique", vertex)
    return provenance


def infer_verification_origin(verification: dict[str, Any] | None) -> str:
    if not verification:
        return "missing"
    explicit = verification.get("verification_origin")
    if explicit:
        return str(explicit)
    haystack = " ".join(
        str(verification.get(field) or "")
        for field in ("verification_kind", "stdout", "stderr", "stdout_tail", "stderr_tail")
    ).lower()
    if "synthetic" in haystack or "smoke" in haystack:
        return "synthetic_smoke"
    return "lean_produced"


def is_hard_audit_finding(finding: str) -> bool:
    if finding.startswith("observation:"):
        return False
    if "synthetic smoke" in finding:
        return False
    if finding.startswith("transport review:"):
        return False
    return True


def audit_build(
    build: dict[str, Any] | None,
    verification: dict[str, Any] | None,
    provenance: dict[str, Any] | None = None,
) -> tuple[str, list[str]]:
    findings: list[str] = []
    if not build:
        return "fail", ["missing BuildPacket"]
    if build.get("authority") != "build_checked":
        findings.append("BuildPacket authority is not build_checked")
    if build.get("state") != "passed":
        findings.append(f"BuildPacket state is {build.get('state')!r}, not 'passed'")
    if str(build.get("representation_class") or "") == "shadow":
        findings.append("BuildPacket is shadow representation")
    if not verification:
        findings.append("referenced VerificationPacket is missing")
    elif verification.get("authority") != "lean_checked":
        findings.append("referenced VerificationPacket authority is not lean_checked")

    origin = infer_verification_origin(verification)
    if origin == "synthetic_smoke":
        findings.append("verification anchor is synthetic smoke, so audit cannot be full pass")

    proposal = (provenance or {}).get("proposal") or {}
    if proposal:
        backend_kind = str(proposal.get("backend_kind") or "unknown")
        hermes_role = str(proposal.get("hermes_role") or "unknown")
        provider_policy = str(proposal.get("provider_contact_policy") or "unknown")
        findings.append(f"observation: upstream proposal backend_kind={backend_kind}")
        findings.append(f"observation: upstream proposal hermes_role={hermes_role}")
        findings.append(f"observation: upstream provider_contact_policy={provider_policy}")
        if backend_kind in {"gemini_cli", "copilot_cli"}:
            findings.append(f"observation: upstream proposal came from high-temperature symbolic backend {backend_kind}")
        if backend_kind == "provider_api":
            findings.append("transport review: upstream proposal used direct provider_api backend")
        if str(proposal.get("representation_class") or "") == "shadow" and not proposal.get("bridge_packet_key"):
            findings.append("owner/shadow conflict: upstream shadow proposal has no explicit bridge packet")
    else:
        findings.append("observation: no upstream ProposalPacket found in build lineage")

    hard_failures = [item for item in findings if is_hard_audit_finding(item)]
    if hard_failures:
        return "fail", findings
    if findings:
        return "conditional_pass", findings
    return "pass", ["build packet passed conservative audit checks"]


def emit_audit_packet(
    config: AuditBeeConfig,
    task: dict[str, Any],
    *,
    build: dict[str, Any],
    verification: dict[str, Any] | None,
    provenance: dict[str, Any] | None,
    verdict: str,
    findings: list[str],
) -> dict[str, Any]:
    verification_origin = infer_verification_origin(verification)
    proposal = (provenance or {}).get("proposal") or {}
    packet = {
        "schema": "hive.packet.audit.v1",
        "authority": "audit_checked",
        "representation_class": build.get("representation_class") or "owner",
        "representation_depth": build.get("representation_depth") or "operatorial",
        "source_regime": "synthetic_smoke" if verification_origin == "synthetic_smoke" else "theorem_lane",
        "audit_origin": "auditbee",
        "build_key": build["packet_key"],
        "verdict": verdict,
        "findings": findings,
        "verification_key": build.get("verification_key"),
        "verification_origin": verification_origin,
        "upstream_backend_kind": proposal.get("backend_kind"),
        "upstream_backend_identity": proposal.get("backend_identity"),
        "upstream_hermes_role": proposal.get("hermes_role"),
        "upstream_provider_contact_policy": proposal.get("provider_contact_policy"),
        "promotion_allowed": False,
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
        dependencies=[build],
    )["packet"]


def run_one(config: AuditBeeConfig) -> dict[str, Any]:
    task = claim_audit_task(config)
    if not task:
        return {"status": "idle", "worker_id": config.worker_id, "queue_name": config.queue_name}

    build_key = str(task.get("build_key") or "")
    build = fetch_build_packet(config, build_key)
    verification = None
    provenance: dict[str, Any] = {}
    if build:
        verification_key = str(build.get("verification_key") or "")
        verification = fetch_verification_packet(config, verification_key)
        provenance = fetch_upstream_provenance(config, build_key)
    verdict, findings = audit_build(build, verification, provenance)

    if not build:
        updated_task = queue_tool.fail_task(
            config.hive_endpoint,
            config.hive_database,
            config.hive_username,
            config.hive_password,
            task_key_value=str(task["_key"]),
            worker_id=config.worker_id,
            error_message="audit task references missing BuildPacket",
        )
        return {"status": "failed", "task": updated_task or task, "findings": findings}

    audit_packet = emit_audit_packet(
        config,
        task,
        build=build,
        verification=verification,
        provenance=provenance,
        verdict=verdict,
        findings=findings,
    )
    updated_task = queue_tool.complete_task(
        config.hive_endpoint,
        config.hive_database,
        config.hive_username,
        config.hive_password,
        task_key_value=str(task["_key"]),
        worker_id=config.worker_id,
    )
    return {"status": verdict, "task": updated_task or task, "audit_packet": audit_packet}


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--hive-endpoint", default=DEFAULT_HIVE_ENDPOINT)
    parser.add_argument("--hive-database", default=DEFAULT_HIVE_DATABASE)
    parser.add_argument("--hive-username", default=DEFAULT_HIVE_USERNAME)
    parser.add_argument("--hive-password", default=DEFAULT_HIVE_PASSWORD)
    parser.add_argument("--queue-name", default=DEFAULT_QUEUE)
    parser.add_argument("--worker-id", default=DEFAULT_WORKER_ID)
    parser.add_argument("--lease-seconds", type=int, default=DEFAULT_LEASE_SECONDS)
    parser.add_argument("--once", action="store_true", help="run one audit task and exit")
    parser.add_argument("--poll-interval", type=int, default=15)
    return parser.parse_args()


def config_from_args(args: argparse.Namespace) -> AuditBeeConfig:
    return AuditBeeConfig(
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
