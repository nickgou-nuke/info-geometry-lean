#!/usr/bin/env python3
"""Merge checker check results into declaration-oriented audit telemetry.

This keeps Lean as kernel authority and treats checker packets as policy-gated
lanes with soft/hard fail semantics.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
from typing import Any, Iterable

try:  # Optional dependency.
    import yaml  # type: ignore
except ImportError:  # pragma: no cover
    yaml = None


SCHEMA = "info_geometry.hive_multichecker_report.v1"
DEFAULT_POLICY_PATH = Path(__file__).resolve().with_name("verification_policy.yaml")

DECL_KEYS = (
    "decl",
    "declaration",
    "declaration_name",
    "name",
    "fullName",
    "full_name",
    "theorem",
    "target_decl",
    "target_name",
    "problem",
)

CANONICAL_LANE_BY_TOOL = {
    "leanparanoia": "bee_pauli_policy",
    "safeverify": "bee_ref_impl",
    "socratic": "bee_socratic",
    "socratic_question": "bee_socratic",
    "paperclip": "bee_paperclip",
    "paperclip_adapter": "bee_paperclip",
    "paperclip_adapter_server": "bee_paperclip",
    "hermes_paperclip": "bee_paperclip",
    "lean4_autograder": "bee_ref_impl",
    "autograder": "bee_ref_impl",
    "hive_spec_submission_policy": "bee_promotion",
    "promotion": "bee_promotion",
}

DEFAULT_VERIFICATION_POLICY = {
    "schema": "info_geometry.verification_policy.v1",
    "version": "1",
    "lane_default_tier": "tier_c",
    "lane_tiers": {
        "bee_kernel_replay": "tier_a",
        "bee_ref_impl": "tier_a",
        "bee_pauli_policy": "tier_b",
        "bee_lean_conductivity": "tier_b",
        "bee_semantic_guard": "tier_b",
        "bee_socratic": "tier_b",
        "bee_paperclip": "tier_c",
        "bee_rethlas_refs": "tier_c",
        "bee_promotion": "tier_c",
        "bee_contract": "tier_c",
        "bee_autograder": "tier_c",
    },
    "defaults": {
        "max_soft_failures": 1,
        "escalate_soft_to_hard_after": 2,
        "hard_severity_floor": 95,
        "soft_severity_floor": 70,
    },
    "required_lanes": ["bee_kernel_replay", "bee_ref_impl"],
    "lane_rules": {
        "bee_kernel_replay": {"required": True, "hard": True},
        "bee_ref_impl": {"required": True, "hard": True},
        "bee_autograder": {"required": False, "hard": False},
        "bee_pauli_policy": {"required": True, "hard": False},
        "bee_lean_conductivity": {"required": False, "hard": True, "min_score": 0.7},
        "bee_semantic_guard": {"required": False, "hard": False},
        "bee_paperclip": {"required": False, "hard": False},
        "bee_socratic": {"required": False, "hard": False},
        "bee_rethlas_refs": {"required": False, "hard": False},
        "bee_promotion": {"required": False, "hard": False},
        "bee_contract": {"required": False, "hard": False},
    },
    "targets": {
        "L0": {"required_lanes": ["bee_kernel_replay", "bee_ref_impl", "bee_pauli_policy"]},
        "L1": {"required_lanes": ["bee_kernel_replay", "bee_ref_impl"]},
        "L2": {"required_lanes": ["bee_kernel_replay"]},
    }
}

ToolResult = dict[str, Any]


CANONICAL_LANES = (
    "bee_pauli_policy",
    "bee_ref_impl",
    "bee_autograder",
    "bee_kernel_replay",
    "bee_lean_conductivity",
    "bee_semantic_guard",
    "bee_socratic",
    "bee_paperclip",
    "bee_rethlas_refs",
    "bee_promotion",
    "bee_contract",
)


def _sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def _to_int(value: Any, default: int) -> int:
    try:
        return int(value)
    except Exception:
        return default


def _artifact_metadata(path: Path | None) -> dict[str, Any] | None:
    if path is None or not path.exists():
        return None
    rows = load_json_docs(path)
    schemas = sorted({str(row.get("schema")) for row in rows if isinstance(row.get("schema"), str)})
    try:
        size = path.stat().st_size
        digest = _sha256_file(path)
    except OSError:
        size = 0
        digest = ""
    return {
        "path": str(path),
        "kind": "jsonl" if path.suffix.lower() == ".jsonl" else (path.suffix.lower().strip(".") or "json"),
        "records": len(rows),
        "schemas": schemas,
        "bytes": size,
        "sha256": digest,
    }


def _normalize_lane_health(
    lane_health: dict[str, Any] | None,
    lane_names: Iterable[str],
    lane_tiers: dict[str, str] | None = None,
) -> dict[str, dict[str, Any]]:
    tiers = {str(key): str(value) for key, value in (lane_tiers or {}).items() if key and value}
    normalized: dict[str, dict[str, Any]] = {}
    raw = lane_health or {}
    for lane in lane_names:
        entry = raw.get(lane, {})
        if isinstance(entry, dict):
            normalized[lane] = {
                "executed": bool(entry.get("executed")),
                "skipped": bool(entry.get("skipped")),
                "error": bool(entry.get("error")),
                "timeout": bool(entry.get("timeout")),
                "reason": str(entry.get("reason", "")),
                "records": _to_int(entry.get("records"), 0),
                "failed": _to_int(entry.get("failed"), 0),
                "tier": tiers.get(str(lane), "tier_unknown"),
            }
        else:
            normalized[lane] = {
                "executed": False,
                "skipped": True,
                "error": False,
                "timeout": False,
                "reason": "invalid-health-payload",
                "records": 0,
                "failed": 0,
                "tier": tiers.get(str(lane), "tier_unknown"),
            }

    for lane, entry in raw.items():
        if lane in normalized:
            continue
        if isinstance(entry, dict):
            normalized[lane] = {
                "executed": bool(entry.get("executed")),
                "skipped": bool(entry.get("skipped")),
                "error": bool(entry.get("error")),
                "timeout": bool(entry.get("timeout")),
                "reason": str(entry.get("reason", "")),
                "records": _to_int(entry.get("records"), 0),
                "failed": _to_int(entry.get("failed"), 0),
                "tier": tiers.get(str(lane), "tier_unknown"),
            }
        else:
            normalized[lane] = {
                "executed": False,
                "skipped": True,
                "error": False,
                "timeout": False,
                "reason": "invalid-health-payload",
                "records": 0,
                "failed": 0,
                "tier": tiers.get(str(lane), "tier_unknown"),
            }
    return normalized


def iter_jsonl(path: Path | None) -> Iterable[dict[str, Any]]:
    if path is None or not path.exists():
        return
    with path.open("r", encoding="utf-8") as handle:
        for raw in handle:
            line = raw.strip()
            if not line:
                continue
            try:
                row = json.loads(line)
            except Exception:
                continue
            if isinstance(row, dict):
                yield row


def load_json_docs(path: Path | None) -> list[dict[str, Any]]:
    if path is None or not path.exists():
        return []
    if path.suffix.lower() == ".jsonl":
        return list(iter_jsonl(path))
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
    except Exception:
        return []
    if isinstance(payload, list):
        return [row for row in payload if isinstance(row, dict)]
    if isinstance(payload, dict):
        return [payload]
    return []


def first_string(row: dict[str, Any], keys: tuple[str, ...] = DECL_KEYS) -> str | None:
    for key in keys:
        value = row.get(key)
        if isinstance(value, str) and value:
            return value
    return None


def nested_string(row: dict[str, Any], path: tuple[str, ...]) -> str | None:
    value: Any = row
    for key in path:
        if not isinstance(value, dict):
            return None
        value = value.get(key)
    return value if isinstance(value, str) and value else None


def decl_of(row: dict[str, Any], *, fallback: str | None = None) -> str | None:
    direct = first_string(row)
    if direct:
        return direct
    for path in (
        ("target_info", "name"),
        ("solution_info", "name"),
        ("targetInfo", "name"),
        ("solutionInfo", "name"),
        ("target_info", "constInfo", "name"),
        ("solution_info", "constInfo", "name"),
        ("targetInfo", "constInfo", "name"),
        ("solutionInfo", "constInfo", "name"),
    ):
        found = nested_string(row, path)
        if found:
            return found
    return fallback


def module_of(row: dict[str, Any]) -> str:
    value = row.get("module") or row.get("moduleName") or row.get("module_name")
    return str(value or "")


def kind_of(row: dict[str, Any]) -> str:
    value = row.get("kind") or row.get("constCategory") or row.get("target_kind") or row.get("targetKind")
    return str(value or "")


def lane_of(row: dict[str, Any], fallback_tool: str = "legacy") -> str:
    lane = row.get("lane")
    if isinstance(lane, str) and lane:
        return lane
    source = str(row.get("source") or "")
    if source in CANONICAL_LANE_BY_TOOL:
        return CANONICAL_LANE_BY_TOOL[source]
    if row.get("source") and source == "leanparanoia":
        return "bee_pauli_policy"
    return CANONICAL_LANE_BY_TOOL.get(fallback_tool, fallback_tool)


def message_list(value: Any) -> list[str]:
    if value is None or value is False:
        return []
    if isinstance(value, str):
        return [value] if value else []
    if isinstance(value, list):
        return [str(item) for item in value if item]
    if isinstance(value, dict):
        rows: list[str] = []
        for key, item in value.items():
            for msg in message_list(item):
                rows.append(f"{key}: {msg}")
        return rows
    return [str(value)]


def _to_float(value: Any, default: float) -> float:
    try:
        return float(value)
    except Exception:
        return default


def _extract_score_value(value: Any) -> float | None:
    if value is None:
        return None
    if isinstance(value, (int, float)):
        return float(value)
    if isinstance(value, dict):
        earned = value.get("earned")
        total = value.get("total")
        if isinstance(earned, (int, float)) and isinstance(total, (int, float)):
            if float(total) > 0:
                return float(earned) / float(total)
            return 1.0 if float(earned) == 0 else 0.0
    return None


def _load_policy(path: Path | None) -> dict[str, Any]:
    if path is None or not path.exists():
        return dict(DEFAULT_VERIFICATION_POLICY)
    if yaml is None:
        return dict(DEFAULT_VERIFICATION_POLICY)
    payload = yaml.safe_load(path.read_text(encoding="utf-8"))
    if not isinstance(payload, dict):
        return dict(DEFAULT_VERIFICATION_POLICY)

    merged = dict(DEFAULT_VERIFICATION_POLICY)
    merged["defaults"] = {**merged.get("defaults", {}), **payload.get("defaults", {})}
    if "lane_default_tier" in payload:
        merged["lane_default_tier"] = str(payload["lane_default_tier"])
    merged["lane_tiers"] = {**merged.get("lane_tiers", {}), **(payload.get("lane_tiers") if isinstance(payload.get("lane_tiers"), dict) else {})}
    merged["required_lanes"] = payload.get("required_lanes", merged.get("required_lanes", []))
    merged["lane_rules"] = {
        **merged.get("lane_rules", {}),
        **(payload.get("lane_rules") if isinstance(payload.get("lane_rules"), dict) else {}),
    }
    merged["targets"] = {
        **merged.get("targets", {}),
        **(payload.get("targets") if isinstance(payload.get("targets"), dict) else {}),
    }
    if "version" in payload:
        merged["version"] = str(payload["version"])
    for key, value in payload.items():
        if key in {"defaults", "required_lanes", "lane_rules", "targets", "schema", "version"}:
            continue
        merged[key] = value
    return merged


def required_lanes(policy: dict[str, Any], target_class: str | None) -> list[str]:
    lanes: list[str] = list(policy.get("required_lanes") or [])
    if target_class:
        t = target_class.upper()
        target_rules = policy.get("targets", {})
        if isinstance(target_rules, dict):
            rules = target_rules.get(t)
            if isinstance(rules, dict):
                lanes.extend(rules.get("required_lanes") or [])
    out: list[str] = []
    seen: set[str] = set()
    for lane in lanes:
        if not lane or lane in seen:
            continue
        seen.add(lane)
        out.append(str(lane))
    return out


def lane_rule(policy: dict[str, Any], lane: str) -> dict[str, Any]:
    rules = policy.get("lane_rules")
    if isinstance(rules, dict):
        rule = rules.get(lane)
        if isinstance(rule, dict):
            return rule
    return {}


def lane_tier(policy: dict[str, Any], lane: str) -> str:
    tiers = policy.get("lane_tiers")
    if isinstance(tiers, dict):
        value = tiers.get(lane)
        if isinstance(value, str) and value.strip():
            return value.strip()
    return str(policy.get("lane_default_tier", "tier_unknown"))


def _collect_lane_versions(declarations: dict[str, dict[str, Any]], *, policy: dict[str, Any]) -> dict[str, list[str]]:
    observed: dict[str, set[str]] = {str(lane): set() for lane in sorted(policy.get("lane_rules", {}).keys())}
    for entry in declarations.values():
        for lane, result in (entry.get("tools") or {}).items():
            provenance = result.get("provenance")
            if not isinstance(provenance, dict):
                continue
            for key in ("version", "schema"):
                version = provenance.get(key)
                if isinstance(version, str) and version.strip():
                    observed.setdefault(lane, set()).add(version.strip())
    return {lane: sorted(values) for lane, values in observed.items() if values}


def _accumulate_lane_metrics(
    declarations: list[dict[str, Any]],
    by_tool: dict[str, Any],
    lane_health: dict[str, dict[str, Any]],
    *, policy: dict[str, Any], target_class: str | None
) -> dict[str, Any]:
    req_lanes = set(required_lanes(policy, target_class))
    lane_versions = _collect_lane_versions({decl["decl"]: decl for decl in declarations}, policy=policy)
    metrics: dict[str, Any] = {}
    all_lanes = set(lane_health)
    all_lanes.update(by_tool)
    all_lanes.update(req_lanes)

    for lane in sorted(all_lanes):
        lane_health_row = lane_health.get(lane, {})
        lane_decisions = [
            entry["policy"]["lane_decisions"].get(lane)
            for entry in declarations
            if entry.get("policy", {}).get("lane_decisions").get(lane)
        ]
        lane_required = lane in req_lanes
        metrics[lane] = {
            "records": (by_tool.get(lane) or {}).get("records", 0),
            "passed": (by_tool.get(lane) or {}).get("passed", 0),
            "failed": (by_tool.get(lane) or {}).get("failed", 0),
            "hard_failures": sum(1 for row in lane_decisions if row.get("hard")),
            "soft_failures": sum(1 for row in lane_decisions if not row.get("hard") and not row.get("ok")),
            "required": lane_required,
            "executed": bool(lane_health_row.get("executed")),
            "skipped": bool(lane_health_row.get("skipped")),
            "error": bool(lane_health_row.get("error")),
            "timeout": bool(lane_health_row.get("timeout")),
            "records_seen": int(lane_health_row.get("records", 0)),
            "decl_health_failed": sum(
                1
                for row in declarations
                if (lane not in row["policy"]["lane_decisions"] and lane_required)
                or not row["policy"]["lane_decisions"].get(lane, {"ok": True}).get("ok")
            ),
            "versions": lane_versions.get(lane, []),
            "tier": lane_tier(policy, lane),
        }
        denominator = metrics[lane]["records"] or 0
        metrics[lane]["pass_rate"] = metrics[lane]["passed"] / denominator if denominator else 0.0

    return metrics


def add_tool(
    table: dict[str, dict[str, Any]],
    decl: str,
    tool: str,
    result: ToolResult,
    *,
    module: str = "",
    kind: str = "",
) -> None:
    entry = table.setdefault(
        decl,
        {
            "decl": decl,
            "module": module,
            "kind": kind,
            "tools": {},
            "score": {"earned": 0.0, "total": 0.0},
        },
    )
    if module and not entry.get("module"):
        entry["module"] = module
    if kind and not entry.get("kind"):
        entry["kind"] = kind
    entry["tools"][tool] = result
    score = result.get("score")
    if isinstance(score, dict):
        entry["score"]["earned"] += float(score.get("earned") or 0)
        entry["score"]["total"] += float(score.get("total") or 0)


def load_declarations(paths: list[Path]) -> dict[str, dict[str, Any]]:
    table: dict[str, dict[str, Any]] = {}
    for path in paths:
        for row in load_json_docs(path):
            decl = decl_of(row)
            if not decl:
                continue
            table.setdefault(
                decl,
                {
                    "decl": decl,
                    "module": module_of(row),
                    "kind": kind_of(row),
                    "tools": {},
                    "score": {"earned": 0.0, "total": 0.0},
                },
            )
    return table


def contract_result(row: dict[str, Any]) -> ToolResult:
    return {
        "ok": bool(row.get("ok")),
        "checks": [str(check) for check in row.get("checks", [])] or ["contract"],
        "error": None if bool(row.get("ok")) else "; ".join(str(item) for item in row.get("reasons", [])),
        "source": str(row.get("lane") or row.get("source") or "contract"),
        "lane": str(row.get("lane") or row.get("source") or "contract"),
        "raw_id": row.get("id"),
        "score": row.get("score"),
        "severity": _to_float(row.get("severity"), 0.0),
        "evidence": row.get("evidence") if isinstance(row.get("evidence"), list) else [],
        "authority_level": str(row.get("authority_level") or "heuristic"),
        "provenance": row.get("provenance") if isinstance(row.get("provenance"), dict) else {},
    }


def leanparanoia_result(row: dict[str, Any]) -> ToolResult:
    findings = row.get("findings") if isinstance(row.get("findings"), list) else []
    messages = [str(item.get("message") or item) for item in findings]
    return {
        "ok": bool(row.get("success")),
        "checks": [str(item.get("check") or "leanparanoia") for item in findings] or ["leanparanoia"],
        "error": "; ".join(messages) if messages else None,
        "source": "leanparanoia",
        "lane": "bee_pauli_policy",
        "raw_id": row.get("id"),
        "score": None,
        "severity": 95 if not bool(row.get("success")) else 0,
        "evidence": [
            {
                "path": str(row.get("source_path") or ""),
                "line": int(row.get("line") or 0),
                "snippet": "",
                "declaration": str(row.get("theorem") or row.get("declaration") or ""),
            }
        ],
        "authority_level": "policy",
        "provenance": {
            "tool": "leanparanoia",
            "schema": str(row.get("schema") or ""),
            "source": "leanparanoia_audit_bridge",
            "cmd": row.get("command") or [],
            "returncode": row.get("returncode"),
        },
    }


def safeverify_result(row: dict[str, Any]) -> ToolResult:
    failure = row.get("failure_mode") or row.get("failureMode")
    return {
        "ok": bool(row.get("success")),
        "checks": ["kind", "type", "axioms", "target-submission"],
        "error": None if row.get("success") else str(failure or "SafeVerify failed"),
        "source": "safeverify",
        "lane": "bee_ref_impl",
        "raw_id": row.get("id"),
        "score": None,
        "severity": 100 if not bool(row.get("success")) else 0,
        "evidence": [
            {
                "path": str(row.get("source_path") or ""),
                "line": 0,
                "snippet": str(failure or ""),
                "declaration": str(row.get("declaration") or row.get("theorem") or ""),
            }
        ],
        "authority_level": "policy",
        "provenance": {
            "tool": "safeverify",
            "schema": str(row.get("schema") or ""),
            "source": "safeverify_audit_bridge",
            "target_olean": str(row.get("target_olean") or ""),
            "submission_olean": str(row.get("submission_olean") or ""),
        },
    }


def autograder_problem_result(problem: dict[str, Any], parent: dict[str, Any]) -> ToolResult:
    return {
        "ok": bool(problem.get("passed")),
        "checks": ["autograder-score"],
        "error": None if problem.get("passed") else str(problem.get("message") or problem.get("status") or "autograder failed"),
        "source": "lean4_autograder",
        "lane": "bee_autograder",
        "raw_id": problem.get("id") or parent.get("id"),
        "score": {"earned": float(problem.get("earned") or 0), "total": float(problem.get("points") or 0)},
        "severity": 65 if not bool(problem.get("passed")) else 0,
        "evidence": [
            {
                "path": str(problem.get("path") or parent.get("path") or ""),
                "line": int(problem.get("line") or 0),
                "snippet": str(problem.get("message") or ""),
                "declaration": str(problem.get("name") or problem.get("target_name") or ""),
            }
        ],
        "authority_level": "policy",
        "provenance": {"tool": "lean4_autograder", "source": "lean4_autograder"},
    }


def promotion_result(row: dict[str, Any]) -> ToolResult:
    violations = row.get("violations") if isinstance(row.get("violations"), list) else []
    messages = [str(item.get("message") or item) for item in violations]
    return {
        "ok": bool(row.get("promotion_allowed")),
        "checks": [str(item.get("code") or "promotion-gate") for item in violations] or ["promotion-gate"],
        "error": None if row.get("promotion_allowed") else "; ".join(messages),
        "source": "hive_spec_submission_policy",
        "lane": "bee_promotion",
        "raw_id": row.get("packet_key"),
        "score": row.get("autograder_points") if isinstance(row.get("autograder_points"), dict) else None,
        "severity": 90 if not bool(row.get("promotion_allowed")) else 0,
        "evidence": [
            {
                "path": str(row.get("path") or ""),
                "line": 0,
                "snippet": "",
                "declaration": str(row.get("spec_id") or ""),
            }
        ],
        "authority_level": "policy",
        "provenance": {"tool": "promotion", "source": "hive_spec_submission_policy"},
    }


def _is_contract_row(row: dict[str, Any]) -> bool:
    return row.get("schema") == "info_geometry.verification_result.v1" or "lane" in row or "checks" in row and "reasons" in row


def _merge_rows(
    table: dict[str, dict[str, Any]],
    rows: list[dict[str, Any]],
    *,
    fallback_tool: str,
) -> None:
    for row in rows:
        if not _is_contract_row(row):
            continue
        decl = decl_of(row, fallback=f"{fallback_tool}:{id(row)}")
        if not decl:
            continue
        add_tool(
            table,
            decl,
            lane_of(row, fallback_tool=fallback_tool),
            contract_result(row),
            module=module_of(row),
            kind=kind_of(row),
        )


def _collect_rows(rows: list[dict[str, Any]]) -> tuple[list[dict[str, Any]], list[dict[str, Any]]]:
    contract_rows: list[dict[str, Any]] = []
    legacy_rows: list[dict[str, Any]] = []
    for row in rows:
        if _is_contract_row(row):
            contract_rows.append(row)
        else:
            legacy_rows.append(row)
    return contract_rows, legacy_rows


def merge_reports(
    *,
    decl_paths: list[Path],
    leanparanoia_path: Path | None = None,
    safeverify_path: Path | None = None,
    autograder_path: Path | None = None,
    promotion_path: Path | None = None,
    lane_contract_paths: list[Path] | None = None,
    policy_path: Path | None = None,
    target_class: str | None = None,
    lane_health: dict[str, Any] | None = None,
) -> dict[str, Any]:
    policy = _load_policy(policy_path)
    req_lanes = required_lanes(policy, target_class)
    table = load_declarations(decl_paths)
    contract_paths = list(lane_contract_paths or [])

    # LeanParanoia lane
    lp_contract_rows, lp_legacy_rows = _collect_rows(load_json_docs(leanparanoia_path))
    _merge_rows(table, lp_contract_rows, fallback_tool="bee_pauli_policy")
    for row in lp_legacy_rows:
        decl = decl_of(row)
        if decl:
            add_tool(
                table,
                decl,
                lane_of(row, fallback_tool="leanparanoia"),
                leanparanoia_result(row),
                module=module_of(row),
                kind=kind_of(row),
            )

    # SafeVerify lane
    sv_contract_rows, sv_legacy_rows = _collect_rows(load_json_docs(safeverify_path))
    _merge_rows(table, sv_contract_rows, fallback_tool="bee_ref_impl")
    for index, row in enumerate(sv_legacy_rows):
        decl = decl_of(row, fallback=f"safeverify:{index}")
        if decl:
            add_tool(
                table,
                decl,
                lane_of(row, fallback_tool="safeverify"),
                safeverify_result(row),
                module=module_of(row),
                kind=kind_of(row),
            )

    # Autograder/problem lane
    ag_contract_rows, ag_legacy_rows = _collect_rows(load_json_docs(autograder_path))
    _merge_rows(table, ag_contract_rows, fallback_tool="bee_autograder")
    for row in ag_legacy_rows:
        problems = row.get("problems") if isinstance(row.get("problems"), list) else []
        if problems:
            for problem in problems:
                if not isinstance(problem, dict):
                    continue
                decl = decl_of(problem, fallback=str(problem.get("name") or "autograder_problem"))
                if decl:
                    add_tool(
                        table,
                        decl,
                        "bee_autograder",
                        autograder_problem_result(problem, row),
                        kind=str(problem.get("kind") or ""),
                    )
        else:
            decl = decl_of(row, fallback=str(row.get("id") or "autograder"))
            add_tool(
                table,
                decl,
                "bee_autograder",
                {
                    "ok": bool(row.get("passed")),
                    "checks": ["autograder-report"],
                    "error": None if row.get("passed") else "autograder report failed",
                    "source": "lean4_autograder",
                    "lane": "bee_autograder",
                    "raw_id": row.get("id"),
                    "severity": 65 if not bool(row.get("passed")) else 0,
                    "evidence": [
                        {
                            "path": str(row.get("path") or ""),
                            "line": 0,
                            "snippet": str(row.get("status") or ""),
                            "declaration": str(row.get("name") or ""),
                        }
                    ],
                    "authority_level": "policy",
                    "score": {
                        "earned": float(row.get("earned_points") or 0),
                        "total": float(row.get("total_points") or 0),
                    },
                    "provenance": {"tool": "lean4_autograder", "source": "autograder"},
                },
            )

    # Promotion lane
    gate_contract_rows, gate_legacy_rows = _collect_rows(load_json_docs(promotion_path))
    _merge_rows(table, gate_contract_rows, fallback_tool="bee_promotion")
    for row in gate_legacy_rows:
        decl = decl_of(row, fallback=f"promotion:{row.get('spec_id', 'spec')}::{row.get('submission_id', 'submission')}")
        add_tool(table, decl, lane_of(row, fallback_tool="bee_promotion"), promotion_result(row))

    for path in contract_paths:
        _merge_rows(table, load_json_docs(path), fallback_tool="bee_contract")

    declarations = []
    defaults = policy.get("defaults", {})
    max_soft = int(defaults.get("max_soft_failures", 0))
    soft_severity = float(defaults.get("soft_severity_floor", 70))
    hard_severity = float(defaults.get("hard_severity_floor", 95))
    escalate_soft = int(defaults.get("escalate_soft_to_hard_after", 2))

    for decl in sorted(table):
        entry = table[decl]
        tools = entry.get("tools") or {}
        lane_decisions: dict[str, Any] = {}
        soft_fail_count = 0
        hard_fail_count = 0

        for lane, result in tools.items():
            passed = bool(result.get("ok"))
            severity = _to_float(result.get("severity"), 0.0)
            score = _extract_score_value(result.get("score"))
            rule = lane_rule(policy, lane)
            min_score = rule.get("min_score")
            if passed and min_score is not None and score is not None:
                try:
                    min_score_v = float(min_score)
                except Exception:
                    min_score_v = None
                else:
                    if score < min_score_v:
                        passed = False
                        result["error"] = f"score-below-minimum: {score} < {min_score_v}"
                        result["ok"] = False
                        severity = max(severity, _to_float(rule.get("min_score_severity"), hard_severity))
            if passed:
                lane_decisions[lane] = {"ok": True, "hard": False, "severity": severity}
                continue

            if bool(rule.get("hard")) or severity >= hard_severity:
                hard_fail_count += 1
                lane_decisions[lane] = {"ok": False, "hard": True, "severity": severity, "reason": "hard-rule"}
            else:
                soft_fail_count += 1
                lane_decisions[lane] = {"ok": False, "hard": False, "severity": severity, "reason": "soft-rule"}

        missing_required = [lane for lane in req_lanes if lane not in tools]
        hard_fail_count += len(missing_required)
        for lane in missing_required:
            lane_decisions[lane] = {"ok": False, "hard": True, "severity": hard_severity, "reason": "missing-required-lane"}

        if soft_fail_count >= escalate_soft or (max_soft > 0 and soft_fail_count > max_soft):
            hard_fail_count += 1

        ok = hard_fail_count == 0 and (max_soft == 0 or soft_fail_count <= max_soft)

        errors = []
        for result in tools.values():
            if result.get("error"):
                errors.append(str(result.get("error")))
            elif not result.get("ok"):
                errors.append("failed")
        checks = sorted({str(check) for result in tools.values() for check in result.get("checks", [])})

        declarations.append(
            {
                "decl": decl,
                "module": entry.get("module") or "",
                "kind": entry.get("kind") or "",
                "ok": ok,
                "tools": tools,
                "score": entry.get("score") or {"earned": 0.0, "total": 0.0},
                "checks": checks,
                "error": "; ".join(errors) if errors else None,
                "policy": {
                    "required_lanes": req_lanes,
                    "required_missing": missing_required,
                    "soft_failures": soft_fail_count,
                    "hard_failures": hard_fail_count,
                    "escalated_to_hard": soft_fail_count >= escalate_soft or (max_soft > 0 and soft_fail_count > max_soft),
                    "lane_decisions": lane_decisions,
                },
            }
        )

    tool_names = sorted({tool for row in declarations for tool in row["tools"]})
    by_tool = {}
    for tool in tool_names:
        rows = [row for row in declarations if tool in row["tools"]]
        by_tool[tool] = {
            "records": len(rows),
            "passed": sum(1 for row in rows if row["tools"][tool].get("ok")),
            "failed": sum(1 for row in rows if not row["tools"][tool].get("ok")),
        }

    failed_hard = sum(1 for row in declarations if row["policy"]["hard_failures"] > 0)
    failed_soft = sum(
        1
        for row in declarations
        if row["policy"]["hard_failures"] == 0 and row["policy"]["soft_failures"] > 0 and (max_soft == 0 or row["policy"]["soft_failures"] > max_soft)
    )

    contract_artifacts = [_artifact_metadata(path) for path in contract_paths]
    contract_artifacts = [artifact for artifact in contract_artifacts if artifact is not None]

    lane_names = set(CANONICAL_LANES)
    lane_names.update(policy.get("lane_rules", {}).keys())
    lane_names.update(req_lanes)
    for entry in declarations:
        lane_names.update(entry["tools"].keys())
        lane_names.update(entry["policy"]["lane_decisions"].keys())
    lane_tier_map = {str(item): lane_tier(policy, str(item)) for item in lane_names if item}
    lane_health_report = _normalize_lane_health(
        lane_health,
        sorted(str(item) for item in lane_names if item),
        lane_tiers=lane_tier_map,
    )
    lane_metrics = _accumulate_lane_metrics(
        declarations,
        by_tool,
        lane_health_report,
        policy=policy,
        target_class=target_class,
    )

    return {
        "schema": SCHEMA,
        "policy": {
            "path": str(policy_path or DEFAULT_POLICY_PATH),
            "version": str(policy.get("version", "default")),
            "hash": _sha256_file(Path(policy_path)) if policy_path and Path(policy_path).exists() else "",
            "target_class": target_class or "default",
            "lane_tiers": lane_tier_map,
            "lane_default_tier": str(policy.get("lane_default_tier", "tier_unknown")),
            "required_lanes": req_lanes,
            "defaults": defaults,
            "schema": str(policy.get("schema", "")),
        },
        "contract_artifacts": contract_artifacts,
        "lane_health": lane_health_report,
        "lane_metrics": lane_metrics,
        "summary": {
            "total_declarations": len(declarations),
            "with_checker_data": sum(1 for row in declarations if row["tools"]),
            "passed_all": sum(1 for row in declarations if row["ok"]),
            "failed_any": sum(1 for row in declarations if row["tools"] and not row["ok"]),
            "failed_hard": failed_hard,
            "failed_soft": failed_soft,
            "missing_checker_data": sum(1 for row in declarations if not row["tools"]),
            "by_tool": by_tool,
        },
        "declarations": declarations,
        "authority_boundary": {
            "merged_report_is_audit_telemetry": True,
            "not_a_proof_certificate": True,
            "lean_remains_proof_authority": True,
            "promotion_requires_hive_gates": True,
        },
    }


def markdown_report(report: dict[str, Any]) -> str:
    summary = report["summary"]
    lines = [
        "# Hive Multi-Checker Report",
        "",
        "This report merges checker telemetry using lane authority and policy gates.",
        "",
        "## Summary",
        "",
        f"- Total declarations: {summary['total_declarations']}",
        f"- With checker data: {summary['with_checker_data']}",
        f"- Passed all supplied checks: {summary['passed_all']}",
        f"- Failed any supplied check: {summary['failed_any']}",
        f"- Failed hard: {summary['failed_hard']}",
        f"- Soft-only misses: {summary['failed_soft']}",
        f"- Missing checker data: {summary['missing_checker_data']}",
        "",
        "## Tools",
        "",
    ]
    for tool, stats in sorted(summary.get("by_tool", {}).items()):
        lines.append(
            f"- `{tool}`: {stats['passed']} passed, {stats['failed']} failed, {stats['records']} records"
        )
    lines.extend(["", "## Failures", ""])
    failures = [row for row in report["declarations"] if row["tools"] and not row["ok"]]
    if not failures:
        lines.append("No supplied checker failures.")
    else:
        for row in failures[:200]:
            lines.append(f"- `{row['decl']}`: {row['error'] or 'failed'}")
    lines.extend(["", "## Policy", ""])
    for row in report["declarations"]:
        policy = row.get("policy") or {}
        if policy.get("hard_failures"):
            lines.append(f"- `{row['decl']}` hard-failed: required={policy.get('required_missing', [])}")
        elif policy.get("soft_failures"):
            lines.append(f"- `{row['decl']}` soft failures: {policy.get('soft_failures')}")

    lines.extend(["", "## Lane Health", ""])
    for lane, health in sorted((report.get("lane_health") or {}).items()):
        lines.append(
            f"- `{lane}`: executed={health.get('executed')}, skipped={health.get('skipped')}, "
            f"error={health.get('error')}, timeout={health.get('timeout')}, records={health.get('records')}, failed={health.get('failed')}"
        )
    return "\n".join(lines)


def write_outputs(report: dict[str, Any], json_out: Path, md_out: Path | None) -> None:
    json_out.parent.mkdir(parents=True, exist_ok=True)
    json_out.write_text(json.dumps(report, indent=2, ensure_ascii=True, sort_keys=True) + "\n", encoding="utf-8")
    if md_out:
        md_out.parent.mkdir(parents=True, exist_ok=True)
        md_out.write_text(markdown_report(report), encoding="utf-8")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--decls", type=Path, action="append", default=[], help="Declaration JSON/JSONL artifact used to seed rows")
    parser.add_argument("--leanparanoia-jsonl", type=Path)
    parser.add_argument("--safeverify-jsonl", type=Path)
    parser.add_argument("--autograder-jsonl", type=Path)
    parser.add_argument("--promotion-json", type=Path)
    parser.add_argument("--lane-contract", type=Path, action="append", default=[], help="Unified contract JSON/JSONL input")
    parser.add_argument("--policy", type=Path, default=DEFAULT_POLICY_PATH)
    parser.add_argument("--target-class", choices=["L0", "l0", "L1", "l1", "L2", "l2"], default=None)
    parser.add_argument("--json-out", type=Path, required=True)
    parser.add_argument("--md-out", type=Path)
    args = parser.parse_args()

    report = merge_reports(
        decl_paths=list(args.decls),
        leanparanoia_path=args.leanparanoia_jsonl,
        safeverify_path=args.safeverify_jsonl,
        autograder_path=args.autograder_jsonl,
        promotion_path=args.promotion_json,
        lane_contract_paths=args.lane_contract,
        policy_path=args.policy,
        target_class=(args.target_class.upper() if args.target_class else None),
    )
    write_outputs(report, args.json_out, args.md_out)
    print(json.dumps(report["summary"], indent=2, ensure_ascii=True, sort_keys=True))
    return 0 if report["summary"]["failed_hard"] == 0 and report["summary"]["failed_soft"] == 0 else 2


if __name__ == "__main__":
    raise SystemExit(main())
