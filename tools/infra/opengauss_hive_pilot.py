#!/usr/bin/env python3
"""Run one replayable, local OpenGauss/Hive verification pilot.

Archon may schedule this command, but it does not provide mathematical
authority.  Every authoritative stage below is produced by a repository tool
or by Lean itself.  The runner never edits an owner file and never promotes a
candidate; ``promote`` is only a decision recorded after independent evidence
is supplied with ``--allow-promotion``.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
import subprocess
import sys
import re
import tempfile
import time
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[2]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))
SRC = ROOT / "src"
if str(SRC) not in sys.path:
    sys.path.insert(0, str(SRC))

from tools.build_lock import acquire_build_lock  # noqa: E402
from tools.infra.opengauss_ground_truth_contract import (  # noqa: E402
    canonical_digest,
    load_and_validate_contract,
    _qualified_declaration_heads,
)
from tools.infra.hive_packet_validate import (  # noqa: E402
    SCHEMA_BY_KIND,
    build_store,
    validate_packet,
)


def now() -> str:
    return datetime.now(timezone.utc).isoformat()


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def sha256_file(path: Path) -> str:
    return sha256_bytes(path.read_bytes())


def write_json(path: Path, value: Any) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_suffix(path.suffix + ".tmp")
    temporary.write_text(
        json.dumps(value, ensure_ascii=False, sort_keys=True, indent=2) + "\n",
        encoding="utf-8",
    )
    temporary.replace(path)


def run_command(
    command: list[str], *, cwd: Path, lock: bool = False, timeout_seconds: float = 120.0,
) -> dict[str, Any]:
    def execute() -> subprocess.CompletedProcess[str]:
        return subprocess.run(
            command, cwd=cwd, text=True, capture_output=True, check=False,
            timeout=timeout_seconds,
        )

    if lock:
        with acquire_build_lock(None, f"opengauss-hive-pilot:{os.getpid()}", block=True):
            result = execute()
    else:
        result = execute()
    output = (result.stdout + result.stderr).strip()
    return {
        "command": command,
        "exit_code": result.returncode,
        "success": result.returncode == 0,
        "output": output[-20000:],
        "timed_out": False,
    }


def run_command_safe(
    command: list[str], *, cwd: Path, lock: bool = False, timeout_seconds: float = 120.0,
) -> dict[str, Any]:
    try:
        return run_command(command, cwd=cwd, lock=lock, timeout_seconds=timeout_seconds)
    except subprocess.TimeoutExpired as exc:
        def as_text(value: str | bytes | None) -> str:
            if value is None:
                return ""
            if isinstance(value, bytes):
                return value.decode("utf-8", errors="replace")
            return value

        output = (as_text(exc.stdout) + as_text(exc.stderr)).strip()
        return {
            "command": command,
            "exit_code": None,
            "success": False,
            "timed_out": True,
            "output": output[-20000:],
        }


def require_repo_relative(path: Path, *, label: str) -> Path:
    resolved = path.resolve()
    try:
        relative = resolved.relative_to(ROOT.resolve())
    except ValueError as exc:
        raise ValueError(f"{label} must be inside the repository: {path}") from exc
    if ".." in relative.parts:
        raise ValueError(f"{label} contains traversal: {path}")
    return resolved


def require_sandbox_candidate(path: Path) -> Path:
    resolved = path.resolve()
    if path.is_symlink():
        raise ValueError("candidate symlinks are not permitted")
    allowed = [ROOT / "scratch", ROOT / "tmp"]
    if not any(resolved == base.resolve() or base.resolve() in resolved.parents for base in allowed):
        raise ValueError("candidate must be under repository scratch/ or tmp/")
    if resolved.suffix != ".lean":
        raise ValueError("candidate must be a Lean source file")
    if not resolved.is_file():
        raise ValueError(f"candidate does not exist: {resolved}")
    return resolved


def require_output_dir(path: Path) -> Path:
    resolved = path.resolve()
    allowed = [ROOT / "scratch", ROOT / "tmp"]
    if not any(
        resolved == base.resolve() or base.resolve() in resolved.parents
        for base in allowed
    ):
        raise ValueError("output directory must be under repository scratch/ or tmp/")
    return resolved


def load_independent_evidence(
    path: Path,
    *,
    role: str,
    contract_hash: str,
    candidate_hash: str,
    run_id: str,
    snapshot_hash: str,
) -> dict[str, Any]:
    value = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(value, dict):
        raise ValueError(f"{role} evidence must be a JSON object")
    kind = str(value.get("kind") or "")
    schema_path = SCHEMA_BY_KIND.get(kind)
    if schema_path is None:
        raise ValueError(f"{role} evidence kind is not a repository Hive schema: {kind!r}")
    schema_errors = validate_packet(value, schema_path, build_store())
    if schema_errors:
        raise ValueError(f"{role} evidence failed {schema_path.name}: " + "; ".join(schema_errors))
    if role in {"A-A", "QA-A"} and kind != "AuditPacket":
        raise ValueError(f"{role} evidence must use the repository AuditPacket schema")
    if role == "promotion" and kind != "PromotionDecisionPacket":
        raise ValueError("promotion evidence must use the repository PromotionDecisionPacket schema")
    if value.get("review_role") != role:
        raise ValueError(f"{role} evidence must declare review_role={role!r}")
    agent_id = value.get("agent_id") or value.get("worker_id")
    if not isinstance(agent_id, str) or not agent_id.strip():
        raise ValueError(f"{role} evidence requires a non-empty agent_id")
    for field in (
        "session_id", "origin_run_id", "context_sha256", "environment_fingerprint",
        "tool_invocation", "review_output_sha256",
    ):
        if not isinstance(value.get(field), str) or not value[field].strip():
            raise ValueError(f"{role} evidence requires a non-empty {field}")
    if value.get("fresh_context") is not True:
        raise ValueError(f"{role} evidence must declare fresh_context=true")
    verdict = (
        value.get("verdict") or value.get("outcome") or value.get("audit_outcome")
        or value.get("audit_decision") or value.get("decision")
    )
    if str(verdict).lower() not in {"pass", "passed", "approved", "accept"}:
        raise ValueError(f"{role} evidence is not an accepting verdict")
    for field, expected in (
        ("contract_sha256", contract_hash),
        ("candidate_sha256", candidate_hash),
        ("input_packet_sha256", candidate_hash),
        ("run_id", run_id),
        ("source_snapshot_sha256", snapshot_hash),
    ):
        if value.get(field) != expected:
            raise ValueError(f"{role} evidence {field} does not match this pilot")
    expected_stage = {"A-A": "audit", "QA-A": "qa", "promotion": "promotion"}[role]
    if value.get("stage") != expected_stage:
        raise ValueError(f"{role} evidence must declare stage={expected_stage!r}")
    value["evidence_sha256"] = sha256_file(path)
    value["role"] = role
    return value


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--contract", type=Path, required=True)
    parser.add_argument("--candidate", type=Path, required=True)
    parser.add_argument("--output-dir", type=Path, default=ROOT / "tmp" / "opengauss_hive_pilot")
    parser.add_argument("--build-target", help="Optional Lake module target for the locked build gate.")
    parser.add_argument("--audit-evidence", type=Path, help="Independent A-A JSON evidence.")
    parser.add_argument("--qa-evidence", type=Path, help="Independent QA-A JSON evidence.")
    parser.add_argument("--promotion-evidence", type=Path, help="Schema-valid promotion-worker evidence required for promotion.")
    parser.add_argument("--allow-promotion", action="store_true")
    parser.add_argument("--skip-refutation", action="store_true", help="Only for environment diagnosis; never promotable.")
    parser.add_argument("--timeout-seconds", type=float, default=120.0)
    parser.add_argument("--hive-smoke", action="store_true", help="Run an opt-in Hive claim/heartbeat/requeue smoke test.")
    parser.add_argument(
        "--packet-lineage-packet", action="append", default=[],
        help="Packet JSON path for --packet-lineage-smoke; repeat in causal order.",
    )
    parser.add_argument("--packet-lineage-smoke", action="store_true")
    return parser.parse_args()


def axiom_evidence(candidate_path: Path, *, timeout_seconds: float) -> dict[str, Any]:
    """Compile a source-embedded ``#print axioms`` audit for any candidate path."""
    from tools.infra.opengauss_cli import generate_certification_audit

    audit = generate_certification_audit(candidate_path, write_audit=False, repo_root=ROOT)
    if audit.unparsed_declarations:
        return {
            "command": ["lake", "env", "lean", "<embedded-audit>"],
            "exit_code": None,
            "success": False,
            "timed_out": False,
            "output": "Unparsed declaration heads: " + "; ".join(audit.unparsed_declarations),
            "declarations": audit.declarations,
            "unparsed_declarations": audit.unparsed_declarations,
            "axiom_reports": 0,
            "axioms": [],
            "disallowed_axioms": [],
            "status": "failed",
        }
    source = candidate_path.read_text(encoding="utf-8")
    source = re.sub(r"^\s*#print axioms[^\n]*$", "", source, flags=re.MULTILINE)
    audit_source = source.rstrip() + "\n\n" + "\n".join(
        f"#print axioms {declaration}" for declaration in audit.declarations
    ) + "\n"
    with tempfile.TemporaryDirectory(prefix="opengauss-hive-axioms-") as directory:
        audit_path = Path(directory) / "AxiomAudit.lean"
        audit_path.write_text(audit_source, encoding="utf-8")
        checked = run_command_safe(
            ["lake", "env", "lean", str(audit_path)],
            cwd=ROOT, lock=True, timeout_seconds=timeout_seconds,
        )
    reports = re.findall(
        r"depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms",
        checked.get("output", ""), flags=re.DOTALL,
    )
    axioms: set[str] = set()
    for report in reports:
        axioms.update(item.strip() for item in report.split(",") if item.strip())
    allowed = {"propext", "Classical.choice", "Quot.sound"}
    checked.update({
        "declarations": audit.declarations,
        "unparsed_declarations": audit.unparsed_declarations,
        "axiom_reports": len(reports),
        "axioms": sorted(axioms),
        "disallowed_axioms": sorted(axioms - allowed),
        "status": "passed" if checked["success"] and len(reports) == len(audit.declarations) and not (axioms - allowed) else "failed",
    })
    return checked


def candidate_contract_binding(candidate_path: Path, checked_contract: dict[str, Any]) -> dict[str, Any]:
    """Require the candidate's own declaration and result type to match the contract gap."""
    from tools.infra.opengauss_cli import generate_certification_audit
    from tools.infra.opengauss_screener import _top_level_result_type

    audit = generate_certification_audit(candidate_path, write_audit=False, repo_root=ROOT)
    expected_name = str(checked_contract["missing_declaration_name"])
    expected_expression = " ".join(str(checked_contract["pantograph_expression"]).split())
    heads = _qualified_declaration_heads(candidate_path.read_text(encoding="utf-8"))
    matching = heads.get(expected_name, [])
    candidates: list[dict[str, Any]] = []
    for head in matching:
        parsed = _top_level_result_type(str(head.get("lean_statement") or ""))
        if parsed is None:
            continue
        result_type = " ".join(parsed[1].split())
        candidates.append({
            "kind": head.get("kind"),
            "source_line": head.get("source_line"),
            "source_end_line": head.get("source_end_line"),
            "lean_statement": head.get("lean_statement"),
            "result_type": result_type,
            "expression_matches": result_type == expected_expression,
        })
    return {
        "expected_declaration": expected_name,
        "expected_expression": expected_expression,
        "candidate_declarations": audit.declarations,
        "matching_declarations": candidates,
        "status": "passed" if any(item["expression_matches"] for item in candidates) else "failed",
    }


def parse_cli_json(result: dict[str, Any]) -> dict[str, Any]:
    if not result.get("success"):
        raise RuntimeError(result.get("output") or "Hive CLI command failed")
    try:
        value = json.loads(str(result.get("output") or ""))
    except json.JSONDecodeError as exc:
        raise RuntimeError("Hive CLI did not return JSON") from exc
    if not isinstance(value, dict):
        raise RuntimeError("Hive CLI JSON result is not an object")
    return value


def hive_smoke(*, run_id: str, contract_hash: str, candidate_hash: str, timeout_seconds: float) -> dict[str, Any]:
    """Exercise one isolated queue through heartbeat, claim, expiry, requeue, and completion."""
    queue = f"pilot-{run_id[-16:]}"
    cli = [sys.executable, "tools/infra/hive_arango_queue.py"]
    worker_a = f"pilot-worker-a-{run_id[-8:]}"
    worker_b = f"pilot-worker-b-{run_id[-8:]}"
    records: list[dict[str, Any]] = []

    def call(args: list[str]) -> dict[str, Any]:
        result = run_command_safe([*cli, *args], cwd=ROOT, timeout_seconds=timeout_seconds)
        records.append(result)
        return parse_cli_json(result)

    call(["init"])
    call(["heartbeat-worker", "--worker-id", worker_a, "--capability", "pilot", "--queue", queue])
    enqueued = call([
        "enqueue-goal", "--queue-name", queue,
        "--goal-hash-shape", contract_hash,
        "--canonical-shape", candidate_hash,
        "--target-pretty", "bounded OpenGauss Hive pilot",
        "--module", "PilotCandidate", "--goal-index", "0", "--priority", "1.0",
    ])
    first = call(["claim-next", "--worker-id", worker_a, "--queue-name", queue, "--lease-seconds", "1"])
    task = first.get("task") or first.get("claimed_task") or first
    task_key = task.get("_key") or task.get("task_key")
    if not isinstance(task_key, str) or not task_key:
        raise RuntimeError("Hive claim did not return a task key")
    call(["heartbeat-worker", "--worker-id", worker_b, "--capability", "pilot", "--queue", queue])
    time.sleep(2.0)
    reaped = call(["reap-expired-tasks", "--queue-name", queue])
    second = call(["claim-next", "--worker-id", worker_b, "--queue-name", queue, "--lease-seconds", "30"])
    second_task = second.get("task") or second.get("claimed_task") or second
    second_key = second_task.get("_key") or second_task.get("task_key")
    if second_key != task_key:
        raise RuntimeError("Hive requeue did not return the original task key")
    completed = call(["complete-task", "--task-key", task_key, "--worker-id", worker_b])
    return {
        "stage": "hive_smoke",
        "status": "passed",
        "queue": queue,
        "worker_a": worker_a,
        "worker_b": worker_b,
        "task_key": task_key,
        "enqueued": enqueued,
        "reaped": reaped,
        "completed": completed,
        "command_results": records,
    }


def packet_lineage_smoke(paths: list[Path], *, contract_hash: str, candidate_hash: str) -> dict[str, Any]:
    """Validate a supplied candidate→Lean→build→audit→promotion packet chain."""
    if len(paths) != 5:
        raise ValueError("packet-lineage smoke requires exactly five packets in causal order")
    expected_kinds = [
        "TheoremCandidatePacket", "LeanVerificationPacket", "BuildPacket",
        "AuditPacket", "PromotionDecisionPacket",
    ]
    packets: list[dict[str, Any]] = []
    for path, expected_kind in zip(paths, expected_kinds):
        path = require_repo_relative(path, label="packet lineage")
        packet = json.loads(path.read_text(encoding="utf-8"))
        if not isinstance(packet, dict) or packet.get("kind") != expected_kind:
            raise ValueError(f"packet {path} is not {expected_kind}")
        errors = validate_packet(packet, SCHEMA_BY_KIND[expected_kind], build_store())
        if errors:
            raise ValueError(f"packet {path} failed schema validation: " + "; ".join(errors))
        packets.append(packet)
    candidate, verification, build, audit, promotion = packets
    if candidate.get("ground_truth_contract", {}).get("contract_sha256") != contract_hash:
        raise ValueError("candidate packet contract hash does not match pilot")
    for packet in packets:
        if packet.get("contract_sha256") != contract_hash:
            raise ValueError(f"{packet['kind']} does not carry the complete contract hash")
        if packet.get("source_snapshot_sha256") != candidate_hash:
            raise ValueError(f"{packet['kind']} does not carry the exact source snapshot hash")
    ids = [str(packet.get("id") or "") for packet in packets]
    if any(not item for item in ids) or len(set(ids)) != len(ids):
        raise ValueError("packet lineage IDs must be non-empty and distinct")
    def refs(packet: dict[str, Any], field: str) -> list[dict[str, Any]]:
        raw = packet.get(field)
        refs_for_field = raw if isinstance(raw, list) else ([raw] if raw is not None else [])
        return [ref if isinstance(ref, dict) else {"ref": str(ref)} for ref in refs_for_field]

    def require_ref(packet: dict[str, Any], field: str, target: str, role: str) -> None:
        if not any(ref.get("ref") == target and ref.get("role") == role for ref in refs(packet, field)):
            raise ValueError(f"{packet['kind']} lacks exact {field} reference {target} role={role}")

    require_ref(verification, "parent_refs", candidate["id"], "candidate_under_review")
    require_ref(build, "lean_verification_ref", verification["id"], "verification")
    require_ref(audit, "build_ref", build["id"], "build")
    require_ref(promotion, "audit_ref", audit["id"], "audit")
    require_ref(promotion, "evidence_refs", qa["id"], "qa")
    return {
        "stage": "packet_lineage_smoke",
        "status": "passed",
        "packet_ids": ids,
        "packet_kinds": expected_kinds,
        "packet_hashes": [packet.get("packet_hash") for packet in packets],
    }


def main() -> int:
    args = parse_args()
    run_started = now()
    try:
        contract_path = require_repo_relative(args.contract, label="contract")
        candidate_path = require_sandbox_candidate(args.candidate)
        output_dir = require_output_dir(args.output_dir)
        output_dir.mkdir(parents=True, exist_ok=True)

        checked_contract = load_and_validate_contract(contract_path, repo_root=ROOT)
        contract = checked_contract["contract"]
        contract_hash = canonical_digest(contract)
        candidate_bytes = candidate_path.read_bytes()
        candidate_hash = sha256_bytes(candidate_bytes)
        run_id = "pilot_" + sha256_bytes(
            f"{contract_hash}:{candidate_hash}:{time.time_ns()}".encode("utf-8")
        )[:24]
        run_dir = output_dir / run_id
        run_dir.mkdir(parents=True, exist_ok=False)
        snapshot_path = run_dir / "candidate.lean"
        snapshot_path.write_bytes(candidate_bytes)
        snapshot_hash = sha256_file(snapshot_path)
        if snapshot_hash != candidate_hash:
            raise ValueError("candidate snapshot hash changed during capture")

        write_json(run_dir / "00_contract.json", {
            "stage": "contract",
            "status": "passed",
            "contract_path": str(contract_path.relative_to(ROOT)),
            "contract_sha256": contract_hash,
            "source_hashes": checked_contract,
            "scheduler": "archon",
            "scheduler_authority": "orchestration_only",
            "created_at": run_started,
        })

        declaration_binding = candidate_contract_binding(snapshot_path, checked_contract)
        candidate_binding = {
            "candidate_path": str(candidate_path.relative_to(ROOT)),
            "candidate_sha256": candidate_hash,
            "contract_sha256": contract_hash,
            "source_snapshot": str(snapshot_path.relative_to(ROOT)),
            "source_snapshot_sha256": snapshot_hash,
            "input_packet_sha256": candidate_hash,
            "declaration_binding": declaration_binding,
        }
        write_json(run_dir / "candidate_binding.json", candidate_binding)
        if declaration_binding["status"] != "passed":
            raise ValueError(
                "candidate declaration does not match the Ground-Truth Contract: "
                + json.dumps(declaration_binding, ensure_ascii=False, sort_keys=True)
            )

        def assert_snapshot_unchanged() -> None:
            if sha256_file(snapshot_path) != candidate_hash:
                raise ValueError("candidate snapshot changed during verification")

        refutation = {
            "stage": "refutation",
            "status": "skipped" if args.skip_refutation else "failed",
            "authority": "navigation",
        }
        if not args.skip_refutation:
            refutation_run = run_command_safe(
                [sys.executable, "tools/infra/opengauss_cli.py", "refute", str(snapshot_path), "--strict", "--json"],
                cwd=ROOT, timeout_seconds=args.timeout_seconds,
            )
            assert_snapshot_unchanged()
            refutation.update(refutation_run)
            refutation["status"] = "passed" if refutation_run["success"] else "failed"
        write_json(run_dir / "01_refutation.json", refutation)

        lean = {
            "stage": "lean",
            "authority": "lean_checked",
            "status": "blocked",
            "contract_sha256": contract_hash,
            "candidate_sha256": candidate_hash,
        }
        if refutation["status"] == "passed":
            lean.update(run_command_safe(
                ["lake", "env", "lean", str(snapshot_path)], cwd=ROOT, lock=True,
                timeout_seconds=args.timeout_seconds,
            ))
            assert_snapshot_unchanged()
            lean["status"] = "passed" if lean["success"] else "failed"
        else:
            lean["reason"] = "refutation gate did not pass"
        write_json(run_dir / "02_lean_verification.json", lean)

        axioms = {
            "stage": "axioms",
            "authority": "lean_checked",
            "status": "blocked",
            "contract_sha256": contract_hash,
            "candidate_sha256": candidate_hash,
        }
        if lean["status"] == "passed":
            axioms.update(axiom_evidence(snapshot_path, timeout_seconds=args.timeout_seconds))
            axioms["status"] = axioms.get("status", "failed")
        else:
            axioms["reason"] = "Lean verification did not pass"
        write_json(run_dir / "02_axioms.json", axioms)

        build = {
            "stage": "build",
            "authority": "build_checked",
            "status": "deferred",
            "contract_sha256": contract_hash,
            "candidate_sha256": candidate_hash,
        }
        if args.build_target and lean["status"] == "passed" and axioms["status"] == "passed":
            build.update(run_command_safe(
                [sys.executable, "tools/infra/run_locked_lake_build.py", "--wait-for-build-lock", args.build_target],
                cwd=ROOT, timeout_seconds=args.timeout_seconds,
            ))
            assert_snapshot_unchanged()
            build["status"] = "passed" if build["success"] else "failed"
        elif not args.build_target:
            build["reason"] = "no build target supplied"
        else:
            build["reason"] = "Lean or explicit #print axioms verification did not pass"
        write_json(run_dir / "03_build.json", build)

        audit = {"stage": "audit", "status": "deferred", "authority": "audit_checked"}
        qa = {"stage": "qa", "status": "deferred", "authority": "audit_checked"}
        audit_evidence = None
        qa_evidence = None
        promotion_evidence = None
        if args.audit_evidence:
            audit_evidence = load_independent_evidence(
                require_repo_relative(args.audit_evidence, label="audit evidence"), role="A-A",
                contract_hash=contract_hash, candidate_hash=candidate_hash,
                run_id=run_id, snapshot_hash=snapshot_hash,
            )
            audit = {"stage": "audit", "status": "passed", "authority": "audit_checked", **audit_evidence}
        if args.qa_evidence:
            qa_evidence = load_independent_evidence(
                require_repo_relative(args.qa_evidence, label="QA evidence"), role="QA-A",
                contract_hash=contract_hash, candidate_hash=candidate_hash,
                run_id=run_id, snapshot_hash=snapshot_hash,
            )
            qa = {"stage": "qa", "status": "passed", "authority": "audit_checked", **qa_evidence}
        if args.promotion_evidence:
            promotion_evidence = load_independent_evidence(
                require_repo_relative(args.promotion_evidence, label="promotion evidence"), role="promotion",
                contract_hash=contract_hash, candidate_hash=candidate_hash,
                run_id=run_id, snapshot_hash=snapshot_hash,
            )
        write_json(run_dir / "04_audit.json", audit)
        write_json(run_dir / "05_qa.json", qa)

        ids = {
            "producer": "pilot-producer",
            "auditor": (audit_evidence or {}).get("agent_id", ""),
            "qa": (qa_evidence or {}).get("agent_id", ""),
            "promotion": (promotion_evidence or {}).get("agent_id", ""),
        }
        sessions = {
            (audit_evidence or {}).get("session_id", ""),
            (qa_evidence or {}).get("session_id", ""),
        }
        origins = {
            (audit_evidence or {}).get("origin_run_id", ""),
            (qa_evidence or {}).get("origin_run_id", ""),
        }
        contexts = {
            (audit_evidence or {}).get("context_sha256", ""),
            (qa_evidence or {}).get("context_sha256", ""),
        }
        assert_snapshot_unchanged()
        gates_passed = all(
            stage.get("status") == "passed"
            for stage in (refutation, lean, axioms, build, audit, qa)
        )
        independent = bool(
            ids["auditor"]
            and ids["qa"]
            and (not args.allow_promotion or ids["promotion"])
            and len({ids["producer"], ids["auditor"], ids["qa"], ids["promotion"]} - {""}) == (4 if args.allow_promotion else 3)
            and len(sessions) == 2
            and len(origins) == 2
            and len(contexts) == 2
        )
        decision = "promote" if args.allow_promotion and promotion_evidence and gates_passed and independent else "hold"
        promotion = {
            "stage": "promotion",
            "authority": "promoted" if decision == "promote" else "held",
            "decision": decision,
            "promotion_allowed": decision == "promote",
            "reason": (
                "all gates passed with distinct producer, A-A, and QA-A evidence"
                if decision == "promote" else
                "promotion held; complete Lean/build/audit/QA evidence and explicit allowance are required"
            ),
            "worker_ids": ids,
            "promotion_evidence_sha256": (promotion_evidence or {}).get("evidence_sha256", ""),
            "contract_sha256": contract_hash,
            "candidate_sha256": candidate_hash,
        }
        write_json(run_dir / "06_promotion.json", promotion)

        hive_stage = {"stage": "hive_smoke", "status": "deferred"}
        if args.hive_smoke:
            try:
                hive_stage = hive_smoke(
                    run_id=run_id, contract_hash=contract_hash,
                    candidate_hash=candidate_hash, timeout_seconds=args.timeout_seconds,
                )
            except Exception as exc:
                hive_stage = {"stage": "hive_smoke", "status": "failed", "reason": str(exc)}
            write_json(run_dir / "07_hive_smoke.json", hive_stage)
            if hive_stage.get("status") != "passed" and decision == "promote":
                decision = "hold"
                promotion["authority"] = "held"
                promotion["decision"] = decision
                promotion["promotion_allowed"] = False
                promotion["reason"] = "Hive claim/heartbeat/requeue smoke did not pass"
                write_json(run_dir / "06_promotion.json", promotion)

        packet_stage = {"stage": "packet_lineage_smoke", "status": "deferred"}
        if args.packet_lineage_smoke:
            try:
                packet_stage = packet_lineage_smoke(
                    [Path(item) for item in args.packet_lineage_packet],
                    contract_hash=contract_hash, candidate_hash=candidate_hash,
                )
            except Exception as exc:
                packet_stage = {"stage": "packet_lineage_smoke", "status": "failed", "reason": str(exc)}
            write_json(run_dir / "08_packet_lineage_smoke.json", packet_stage)
            if packet_stage.get("status") != "passed" and decision == "promote":
                decision = "hold"
                promotion["authority"] = "held"
                promotion["decision"] = decision
                promotion["promotion_allowed"] = False
                promotion["reason"] = "Packet lineage smoke did not pass"
                write_json(run_dir / "06_promotion.json", promotion)

        manifest = {
            "schema": "info_geometry.opengauss.hive_pilot.v1",
            "run_id": run_id,
            "started_at": run_started,
            "finished_at": now(),
            "scheduler": "archon",
            "scheduler_authority": "orchestration_only",
            "contract_sha256": contract_hash,
            "candidate_sha256": candidate_hash,
            "decision": decision,
            "qms_acceptance": "accepted" if decision == "promote" else "held",
            "process_exit_code": 0,
            "hive_queue": hive_stage.get("queue") if args.hive_smoke else None,
            "hive_task_key": hive_stage.get("task_key") if args.hive_smoke else None,
            "packet_lineage": packet_stage.get("packet_ids") if args.packet_lineage_smoke else None,
            "open_debt": [
                "A-A/QA-A independence is declared metadata; fresh process context is not independently proven.",
                *([] if args.hive_smoke else ["Hive lease/heartbeat/requeue smoke was not run."]),
                *([] if args.packet_lineage_smoke else ["Packet lineage smoke was not run."]),
                "The pilot never integrates owner source or certifies mathematical promotion.",
            ],
            "artifacts": [str(path.relative_to(ROOT)) for path in sorted(run_dir.glob("*.json"))],
        }
        stages = [refutation, lean, axioms, build, audit, qa]
        if args.hive_smoke:
            stages.append(hive_stage)
        if args.packet_lineage_smoke:
            stages.append(packet_stage)
        rejected_stages = [stage["stage"] for stage in stages if stage.get("status") != "passed"]
        timed_out_stages = [stage["stage"] for stage in stages if stage.get("timed_out")]
        if rejected_stages:
            write_json(run_dir / "rejection_manifest.json", {
                "schema": "info_geometry.opengauss.hive_pilot.rejection.v1",
                "run_id": run_id,
                "contract_sha256": contract_hash,
                "candidate_sha256": candidate_hash,
                "rejected_stages": rejected_stages,
                "decision": decision,
                "created_at": now(),
            })
        if timed_out_stages:
            write_json(run_dir / "timeout_manifest.json", {
                "schema": "info_geometry.opengauss.hive_pilot.timeout.v1",
                "run_id": run_id,
                "contract_sha256": contract_hash,
                "candidate_sha256": candidate_hash,
                "timed_out_stages": timed_out_stages,
                "timeout_seconds": args.timeout_seconds,
                "created_at": now(),
            })
        manifest["artifacts"] = [str(path.relative_to(ROOT)) for path in sorted(run_dir.glob("*.json"))]
        write_json(run_dir / "run_manifest.json", manifest)
        print(json.dumps(manifest, ensure_ascii=False, sort_keys=True, indent=2))
        return 0 if decision in {"promote", "hold"} else 1
    except Exception as exc:
        try:
            rejection_dir = require_output_dir(args.output_dir)
            rejection_dir.mkdir(parents=True, exist_ok=True)
            contract_file_hash = ""
            try:
                contract_file = Path(args.contract).resolve()
                if contract_file.is_file():
                    contract_file_hash = sha256_file(contract_file)
            except OSError:
                contract_file_hash = ""
            rejection_fingerprint = sha256_bytes(
                f"{args.contract}:{args.candidate}:{contract_file_hash}:{os.getpid()}:{exc}".encode("utf-8")
            )[:24]
            write_json(
                rejection_dir / (
                    "rejected_"
                    + datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%S%fZ")
                    + "_" + rejection_fingerprint + ".json"
                ),
                {
                    "schema": "info_geometry.opengauss.hive_pilot.rejection.v1",
                    "decision": "reject",
                    "reason": str(exc),
                    "contract_file_sha256": contract_file_hash,
                    "rejection_fingerprint": rejection_fingerprint,
                    "created_at": now(),
                },
            )
        except Exception:
            pass
        print(f"ERROR: {exc}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
