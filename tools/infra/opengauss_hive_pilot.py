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
import time
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[2]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from tools.build_lock import acquire_build_lock  # noqa: E402
from tools.infra.opengauss_ground_truth_contract import (  # noqa: E402
    canonical_digest,
    load_and_validate_contract,
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


def run_command(command: list[str], *, cwd: Path, lock: bool = False) -> dict[str, Any]:
    def execute() -> subprocess.CompletedProcess[str]:
        return subprocess.run(command, cwd=cwd, text=True, capture_output=True, check=False)

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
    agent_id = value.get("agent_id") or value.get("worker_id")
    if not isinstance(agent_id, str) or not agent_id.strip():
        raise ValueError(f"{role} evidence requires a non-empty agent_id")
    for field in ("session_id", "origin_run_id", "context_sha256"):
        if not isinstance(value.get(field), str) or not value[field].strip():
            raise ValueError(f"{role} evidence requires a non-empty {field}")
    verdict = value.get("verdict") or value.get("outcome")
    if str(verdict).lower() not in {"pass", "passed", "approved", "accept"}:
        raise ValueError(f"{role} evidence is not an accepting verdict")
    for field, expected in (
        ("contract_sha256", contract_hash),
        ("candidate_sha256", candidate_hash),
        ("run_id", run_id),
        ("source_snapshot_sha256", snapshot_hash),
    ):
        if value.get(field) != expected:
            raise ValueError(f"{role} evidence {field} does not match this pilot")
    expected_stage = "audit" if role == "A-A" else "qa"
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
    parser.add_argument("--allow-promotion", action="store_true")
    parser.add_argument("--skip-refutation", action="store_true", help="Only for environment diagnosis; never promotable.")
    return parser.parse_args()


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

        write_json(run_dir / "candidate_binding.json", {
            "candidate_path": str(candidate_path.relative_to(ROOT)),
            "candidate_sha256": candidate_hash,
            "contract_sha256": contract_hash,
            "source_snapshot": str(snapshot_path.relative_to(ROOT)),
            "source_snapshot_sha256": snapshot_hash,
        })

        def assert_snapshot_unchanged() -> None:
            if sha256_file(snapshot_path) != candidate_hash:
                raise ValueError("candidate snapshot changed during verification")

        refutation = {
            "stage": "refutation",
            "status": "skipped" if args.skip_refutation else "failed",
            "authority": "navigation",
        }
        if not args.skip_refutation:
            refutation_run = run_command(
                [sys.executable, "tools/infra/opengauss_cli.py", "refute", str(snapshot_path), "--strict", "--json"],
                cwd=ROOT,
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
            lean.update(run_command(["lake", "env", "lean", str(snapshot_path)], cwd=ROOT, lock=True))
            assert_snapshot_unchanged()
            lean["status"] = "passed" if lean["success"] else "failed"
        else:
            lean["reason"] = "refutation gate did not pass"
        write_json(run_dir / "02_lean_verification.json", lean)

        build = {
            "stage": "build",
            "authority": "build_checked",
            "status": "deferred",
            "contract_sha256": contract_hash,
            "candidate_sha256": candidate_hash,
        }
        if args.build_target and lean["status"] == "passed":
            build.update(run_command(
                [sys.executable, "tools/infra/run_locked_lake_build.py", "--wait-for-build-lock", args.build_target],
                cwd=ROOT,
            ))
            assert_snapshot_unchanged()
            build["status"] = "passed" if build["success"] else "failed"
        elif not args.build_target:
            build["reason"] = "no build target supplied"
        else:
            build["reason"] = "Lean verification did not pass"
        write_json(run_dir / "03_build.json", build)

        audit = {"stage": "audit", "status": "deferred", "authority": "audit_checked"}
        qa = {"stage": "qa", "status": "deferred", "authority": "audit_checked"}
        audit_evidence = None
        qa_evidence = None
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
        write_json(run_dir / "04_audit.json", audit)
        write_json(run_dir / "05_qa.json", qa)

        ids = {
            "producer": "pilot-producer",
            "auditor": (audit_evidence or {}).get("agent_id", ""),
            "qa": (qa_evidence or {}).get("agent_id", ""),
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
            for stage in (refutation, lean, build, audit, qa)
        )
        independent = bool(
            ids["auditor"]
            and ids["qa"]
            and len({ids["producer"], ids["auditor"], ids["qa"]}) == 3
            and len(sessions) == 2
            and len(origins) == 2
            and len(contexts) == 2
        )
        decision = "promote" if args.allow_promotion and gates_passed and independent else "hold"
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
            "contract_sha256": contract_hash,
            "candidate_sha256": candidate_hash,
        }
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
            "artifacts": [str(path.relative_to(ROOT)) for path in sorted(run_dir.glob("*.json"))],
        }
        write_json(run_dir / "run_manifest.json", manifest)
        print(json.dumps(manifest, ensure_ascii=False, sort_keys=True, indent=2))
        return 0 if decision in {"promote", "hold"} else 1
    except Exception as exc:
        print(f"ERROR: {exc}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
