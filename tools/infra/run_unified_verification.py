#!/usr/bin/env python3
"""Run all verification lanes and emit an archived unified report."""

from __future__ import annotations

import argparse
import json
import shutil
import sys
from datetime import datetime, timezone
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from tools.infra.hive_multichecker_merge import CANONICAL_LANES, markdown_report, merge_reports
from tools.infra.verification_contract import CONTRACT_VERSION, SCHEMA as CONTRACT_SCHEMA
from tools.infra.verification_contract import read_json_lines
from tools.infra.lanes.lane_leandepviz import run as run_leandepviz
from tools.infra.lanes.lane_paperclip import run as run_paperclip
from tools.infra.lanes.lane_lean_conductivity import run as run_conductivity
from tools.infra.lanes.lane_socratic import run as run_socratic
from tools.infra.lanes.lane_rethlas_refs import run as run_rethlas_refs
from tools.infra.lanes.lane_ulamai_semantic import run as run_semantic_guard
DEFAULT_POLICY = ROOT / "tools" / "infra" / "verification_policy.yaml"
DEFAULT_OUTPUT_ROOT = ROOT / "reports" / "verification"
LANE_HEALTH_LANES = ("bee_pauli_policy", "bee_ref_impl", "bee_kernel_replay", "bee_semantic_guard", "bee_rethlas_refs")
LANE_HEALTH_LANES = tuple(sorted(set(CANONICAL_LANES) | set(LANE_HEALTH_LANES)))


def _lane_health_record(reason: str = "") -> dict:
    return {
        "executed": False,
        "skipped": True,
        "error": False,
        "timeout": False,
        "reason": reason,
        "records": 0,
        "failed": 0,
    }


def _set_lane_error(
    lane_health: dict[str, dict],
    lane: str,
    reason: str,
    *,
    timeout: bool = False,
) -> None:
    entry = lane_health.setdefault(lane, _lane_health_record("adapter-error"))
    entry["executed"] = True
    entry["skipped"] = False
    entry["error"] = True
    entry["timeout"] = bool(timeout)
    entry["reason"] = reason


def _set_lane_exec(lane_health: dict[str, dict], lane: str, *, executed: bool, records: int, failed: int, reason: str = "") -> None:
    entry = lane_health.setdefault(lane, _lane_health_record("no-input"))
    entry["executed"] = bool(executed)
    entry["skipped"] = not executed
    entry["error"] = False
    entry["records"] = records
    entry["failed"] = failed
    if executed:
        entry["reason"] = reason or ""
    else:
        entry["reason"] = reason or "input-not-provided"


def _summarize_lane_records(path: Path, requested: bool) -> dict[str, dict[str, int]]:
    if not requested:
        return {}
    if not path.exists():
        return {}
    counts: dict[str, dict[str, int]] = {}
    try:
        for row in read_json_lines(path):
            lane = str(row.get("lane") or "")
            if not lane:
                continue
            entry = counts.setdefault(lane, {"records": 0, "failed": 0})
            entry["records"] += 1
            if not bool(row.get("ok")):
                entry["failed"] += 1
    except Exception:
        return {}
    return counts


def utc_run_id() -> str:
    return datetime.now(tz=timezone.utc).strftime("%Y%m%d_%H%M%S_%f")[:-3]


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--decls", type=Path, action="append", required=True, help="Declaration JSON/JSONL file path")
    parser.add_argument("--leanparanoia-jsonl", type=Path)
    parser.add_argument("--safeverify-jsonl", type=Path)
    parser.add_argument("--kernel-jsonl", type=Path, help="Lean verification packet JSON/JSONL")
    parser.add_argument("--autograder-jsonl", type=Path)
    parser.add_argument("--promotion-json", type=Path)
    parser.add_argument("--mathfulness-json", type=Path, help="mathfulness_audit JSON/JSONL")
    parser.add_argument("--rethlas-json", type=Path, help="Rethlas verification JSON/JSONL")
    parser.add_argument("--conductivity-json", type=Path, help="Lean conductivity artifact (representation-depth/audit JSON/JSONL)")
    parser.add_argument("--socratic-json", type=Path, help="SocraticQuestionPacket/Socratic artifact (JSON/JSONL)")
    parser.add_argument("--paperclip-json", type=Path, help="Paperclip control/event artifact (JSON/JSONL)")
    parser.add_argument("--policy", type=Path, default=DEFAULT_POLICY)
    parser.add_argument("--target-class", choices=["L0", "l0", "L1", "l1", "L2", "l2"], default=None)
    parser.add_argument("--output-root", type=Path, default=DEFAULT_OUTPUT_ROOT)
    parser.add_argument("--run-id", type=str, default="")
    parser.add_argument("--no-lane-wrappers", action="store_true", help="Use legacy rows directly without lane adapters")
    parser.add_argument("--json-out", type=Path, default=None, help="Path to unified report JSON (defaults under run directory)")
    parser.add_argument("--md-out", type=Path, default=None, help="Path to unified report markdown (defaults under run directory)")
    return parser.parse_args()


def write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, ensure_ascii=True, sort_keys=True, indent=2), encoding="utf-8")


def refresh_latest_pointer(output_root: Path, run_dir: Path) -> None:
    latest = output_root / "latest"
    if latest.is_symlink() or latest.is_file():
        latest.unlink()
    elif latest.is_dir():
        shutil.rmtree(latest)
    latest.symlink_to(run_dir.name)


def run(argv: argparse.Namespace) -> int:
    output_root = argv.output_root.resolve()
    output_root.mkdir(parents=True, exist_ok=True)
    run_id = argv.run_id or utc_run_id()
    run_dir = output_root / run_id
    contracts_dir = run_dir / "contracts"
    lane_contracts: list[Path] = []
    lane_summaries: dict[str, dict] = {}
    lane_health: dict[str, dict] = {name: _lane_health_record("not-configured") for name in LANE_HEALTH_LANES}

    if not argv.no_lane_wrappers:
        if argv.leanparanoia_jsonl or argv.safeverify_jsonl or argv.kernel_jsonl:
            out = contracts_dir / "lane_leandepviz.jsonl"
            try:
                lane_summaries["lane_leandepviz"] = run_leandepviz(
                    paranoia_path=argv.leanparanoia_jsonl,
                    safeverify_path=argv.safeverify_jsonl,
                    kernel_path=argv.kernel_jsonl,
                    output=out,
                )
                counts = _summarize_lane_records(
                    out,
                    requested=(
                        argv.leanparanoia_jsonl is not None
                        or argv.safeverify_jsonl is not None
                        or argv.kernel_jsonl is not None
                    ),
                )
                _set_lane_exec(
                    lane_health,
                    "bee_pauli_policy",
                    executed=argv.leanparanoia_jsonl is not None,
                    records=counts.get("bee_pauli_policy", {}).get("records", 0),
                    failed=counts.get("bee_pauli_policy", {}).get("failed", 0),
                    reason="ok" if counts is not None else "",
                )
                _set_lane_exec(
                    lane_health,
                    "bee_ref_impl",
                    executed=argv.safeverify_jsonl is not None,
                    records=counts.get("bee_ref_impl", {}).get("records", 0),
                    failed=counts.get("bee_ref_impl", {}).get("failed", 0),
                    reason="ok" if counts is not None else "",
                )
                _set_lane_exec(
                    lane_health,
                    "bee_kernel_replay",
                    executed=argv.kernel_jsonl is not None,
                    records=counts.get("bee_kernel_replay", {}).get("records", 0),
                    failed=counts.get("bee_kernel_replay", {}).get("failed", 0),
                    reason="ok" if counts is not None else "",
                )
                lane_contracts.append(out)
            except TimeoutError as exc:
                _set_lane_error(
                    lane_health,
                    "bee_pauli_policy",
                    f"lane_leandepviz_timeout: {exc}",
                    timeout=True,
                )
                _set_lane_error(
                    lane_health,
                    "bee_ref_impl",
                    f"lane_leandepviz_timeout: {exc}",
                    timeout=True,
                )
                _set_lane_error(
                    lane_health,
                    "bee_kernel_replay",
                    f"lane_leandepviz_timeout: {exc}",
                    timeout=True,
                )
            except Exception as exc:
                _set_lane_error(lane_health, "bee_pauli_policy", f"lane_leandepviz_failed: {exc}")
                _set_lane_error(lane_health, "bee_ref_impl", f"lane_leandepviz_failed: {exc}")
                _set_lane_error(lane_health, "bee_kernel_replay", f"lane_leandepviz_failed: {exc}")
        if argv.mathfulness_json:
            out = contracts_dir / "lane_semantic_guard.jsonl"
            try:
                lane_summaries["lane_semantic_guard"] = run_semantic_guard(argv.mathfulness_json, out)
                counts = _summarize_lane_records(out, requested=argv.mathfulness_json is not None)
                _set_lane_exec(
                    lane_health,
                    "bee_semantic_guard",
                    executed=True,
                    records=counts.get("bee_semantic_guard", {}).get("records", 0),
                    failed=counts.get("bee_semantic_guard", {}).get("failed", 0),
                    reason="ok",
                )
                lane_contracts.append(out)
            except TimeoutError as exc:
                _set_lane_error(
                    lane_health,
                    "bee_semantic_guard",
                    f"lane_semantic_guard_timeout: {exc}",
                    timeout=True,
                )
            except Exception as exc:
                _set_lane_error(lane_health, "bee_semantic_guard", f"lane_semantic_guard_failed: {exc}")
        if argv.conductivity_json:
            out = contracts_dir / "lane_lean_conductivity.jsonl"
            try:
                lane_summaries["lane_lean_conductivity"] = run_conductivity(argv.conductivity_json, out)
                counts = _summarize_lane_records(out, requested=argv.conductivity_json is not None)
                _set_lane_exec(
                    lane_health,
                    "bee_lean_conductivity",
                    executed=True,
                    records=counts.get("bee_lean_conductivity", {}).get("records", 0),
                    failed=counts.get("bee_lean_conductivity", {}).get("failed", 0),
                    reason="ok",
                )
                lane_contracts.append(out)
            except TimeoutError as exc:
                _set_lane_error(
                    lane_health,
                    "bee_lean_conductivity",
                    f"lane_lean_conductivity_timeout: {exc}",
                    timeout=True,
                )
            except Exception as exc:
                _set_lane_error(lane_health, "bee_lean_conductivity", f"lane_lean_conductivity_failed: {exc}")
        if argv.socratic_json:
            out = contracts_dir / "lane_socratic.jsonl"
            try:
                lane_summaries["lane_socratic"] = run_socratic(argv.socratic_json, out)
                counts = _summarize_lane_records(out, requested=argv.socratic_json is not None)
                _set_lane_exec(
                    lane_health,
                    "bee_socratic",
                    executed=True,
                    records=counts.get("bee_socratic", {}).get("records", 0),
                    failed=counts.get("bee_socratic", {}).get("failed", 0),
                    reason="ok",
                )
                lane_contracts.append(out)
            except TimeoutError as exc:
                _set_lane_error(
                    lane_health,
                    "bee_socratic",
                    f"lane_socratic_timeout: {exc}",
                    timeout=True,
                )
            except Exception as exc:
                _set_lane_error(lane_health, "bee_socratic", f"lane_socratic_failed: {exc}")
        if argv.paperclip_json:
            out = contracts_dir / "lane_paperclip.jsonl"
            try:
                lane_summaries["lane_paperclip"] = run_paperclip(argv.paperclip_json, out)
                counts = _summarize_lane_records(out, requested=argv.paperclip_json is not None)
                _set_lane_exec(
                    lane_health,
                    "bee_paperclip",
                    executed=True,
                    records=counts.get("bee_paperclip", {}).get("records", 0),
                    failed=counts.get("bee_paperclip", {}).get("failed", 0),
                    reason="ok",
                )
                lane_contracts.append(out)
            except TimeoutError as exc:
                _set_lane_error(
                    lane_health,
                    "bee_paperclip",
                    f"lane_paperclip_timeout: {exc}",
                    timeout=True,
                )
            except Exception as exc:
                _set_lane_error(lane_health, "bee_paperclip", f"lane_paperclip_failed: {exc}")
        if argv.rethlas_json:
            out = contracts_dir / "lane_rethlas_refs.jsonl"
            try:
                lane_summaries["lane_rethlas_refs"] = run_rethlas_refs(argv.rethlas_json, out)
                counts = _summarize_lane_records(out, requested=argv.rethlas_json is not None)
                _set_lane_exec(
                    lane_health,
                    "bee_rethlas_refs",
                    executed=True,
                    records=counts.get("bee_rethlas_refs", {}).get("records", 0),
                    failed=counts.get("bee_rethlas_refs", {}).get("failed", 0),
                    reason="ok",
                )
                lane_contracts.append(out)
            except TimeoutError as exc:
                _set_lane_error(
                    lane_health,
                    "bee_rethlas_refs",
                    f"lane_rethlas_refs_timeout: {exc}",
                    timeout=True,
                )
            except Exception as exc:
                _set_lane_error(lane_health, "bee_rethlas_refs", f"lane_rethlas_refs_failed: {exc}")
    else:
        for lane in lane_health:
            lane_health[lane]["reason"] = "no-lane-wrappers"

    json_out = argv.json_out or (run_dir / "unified.json")
    md_out = argv.md_out or (run_dir / "summary.md")

    report = merge_reports(
        decl_paths=list(argv.decls),
        leanparanoia_path=None if (not argv.no_lane_wrappers and argv.leanparanoia_jsonl) else argv.leanparanoia_jsonl,
        safeverify_path=None if (not argv.no_lane_wrappers and argv.safeverify_jsonl) else argv.safeverify_jsonl,
        autograder_path=argv.autograder_jsonl,
        promotion_path=argv.promotion_json,
        lane_contract_paths=lane_contracts,
        policy_path=argv.policy,
        target_class=(argv.target_class.upper() if argv.target_class else None),
        lane_health=lane_health,
    )
    report["contract_version"] = str(CONTRACT_VERSION)
    report["contract_schema"] = str(CONTRACT_SCHEMA)
    report["policy_version"] = str(report["policy"].get("version", ""))
    report["policy_hash"] = str(report["policy"].get("hash", ""))

    report["policy_run"] = {
        "run_id": run_id,
        "lane_contracts": [str(path) for path in lane_contracts],
        "lane_summaries": lane_summaries,
        "lane_health": lane_health,
    }
    report["policy_path"] = str(argv.policy)
    write_json(json_out, report)
    md_out.write_text(markdown_report(report), encoding="utf-8")
    write_json(run_dir / "run_manifest.json", {
        "run_id": run_id,
        "generated_at": utc_run_id(),
        "policy": str(argv.policy),
        "policy_version": str(report["policy"].get("version", "")),
        "policy_hash": str(report["policy"].get("hash", "")),
        "contract_version": str(CONTRACT_VERSION),
        "contract_schema": str(CONTRACT_SCHEMA),
        "input": {
            "decls": [str(x) for x in argv.decls],
            "leanparanoia_jsonl": str(argv.leanparanoia_jsonl) if argv.leanparanoia_jsonl else None,
            "safeverify_jsonl": str(argv.safeverify_jsonl) if argv.safeverify_jsonl else None,
            "kernel_jsonl": str(argv.kernel_jsonl) if argv.kernel_jsonl else None,
            "autograder_jsonl": str(argv.autograder_jsonl) if argv.autograder_jsonl else None,
            "promotion_json": str(argv.promotion_json) if argv.promotion_json else None,
            "mathfulness_json": str(argv.mathfulness_json) if argv.mathfulness_json else None,
            "rethlas_json": str(argv.rethlas_json) if argv.rethlas_json else None,
            "conductivity_json": str(argv.conductivity_json) if argv.conductivity_json else None,
            "socratic_json": str(argv.socratic_json) if argv.socratic_json else None,
            "paperclip_json": str(argv.paperclip_json) if argv.paperclip_json else None,
        },
        "output": {
            "run_dir": str(run_dir),
            "unified_json": str(json_out),
            "summary_md": str(md_out),
        },
        "summary": report["summary"],
        "lane_metrics": report.get("lane_metrics", {}),
    })

    refresh_latest_pointer(output_root, run_dir)
    print(json.dumps(report["summary"], indent=2, ensure_ascii=True, sort_keys=True))
    return 0 if report["summary"]["failed_hard"] == 0 and report["summary"]["failed_soft"] == 0 else 2


def main() -> int:
    return run(parse_args())


if __name__ == "__main__":
    raise SystemExit(main())
