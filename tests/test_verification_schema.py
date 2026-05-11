from __future__ import annotations

import json
from pathlib import Path

from tools.infra.validate_unified_verification_schema import validate_contract_row, validate_report


def test_validate_contract_row_accepts_expected_payload() -> None:
    row = {
        "schema": "info_geometry.verification_result.v1",
        "decl": "Demo.ok",
        "module": "Demo",
        "lane": "bee_kernel_replay",
        "ok": True,
        "severity": 0,
        "checks": ["kernel"],
        "reasons": ["passed"],
        "provenance": {"tool": "lean"},
    }

    assert validate_contract_row(row, "row") == []


def test_validate_report_accepts_minimal_payload(tmp_path: Path) -> None:
    payload = {
        "schema": "info_geometry.hive_multichecker_report.v1",
        "policy": {
            "path": "policy.yaml",
            "version": "1",
            "hash": "",
            "target_class": "default",
            "required_lanes": [],
            "defaults": {},
            "lane_tiers": {"bee_kernel_replay": "tier_a"},
            "lane_default_tier": "tier_c",
            "schema": "info_geometry.verification_policy.v1",
        },
        "summary": {
            "total_declarations": 1,
            "with_checker_data": 1,
            "passed_all": 1,
            "failed_any": 0,
            "failed_hard": 0,
            "failed_soft": 0,
            "missing_checker_data": 0,
            "by_tool": {},
        },
        "declarations": [
            {
                "decl": "Demo.ok",
                "module": "Demo",
                "kind": "theorem",
                "ok": True,
                "tools": {"bee_kernel_replay": {"ok": True, "checks": ["kernel"], "severity": 0}},
                "score": {"earned": 1.0, "total": 1.0},
                "checks": ["kernel"],
                "error": None,
                "policy": {
                    "required_lanes": ["bee_kernel_replay"],
                    "required_missing": [],
                    "soft_failures": 0,
                    "hard_failures": 0,
                    "escalated_to_hard": False,
                    "lane_decisions": {
                        "bee_kernel_replay": {
                            "ok": True,
                            "hard": False,
                            "severity": 0,
                        }
                    },
                },
            }
        ],
        "contract_artifacts": [],
        "lane_health": {"bee_kernel_replay": {"executed": True, "skipped": False, "error": False, "timeout": False, "records": 1, "failed": 0, "reason": "ok", "tier": "tier_a"}},
        "lane_metrics": {
            "bee_kernel_replay": {
                "records": 1,
                "passed": 1,
                "failed": 0,
                "hard_failures": 0,
                "soft_failures": 0,
                "required": False,
                "executed": True,
                "skipped": False,
                "error": False,
                "timeout": False,
                "records_seen": 1,
                "decl_health_failed": 0,
                "versions": ["schema:v1"],
                "tier": "tier_a",
                "pass_rate": 1.0,
            }
        },
    }

    report = tmp_path / "report.json"
    report.write_text(json.dumps(payload), encoding="utf-8")

    assert validate_report(json.loads(report.read_text(encoding="utf-8")), report) == []
