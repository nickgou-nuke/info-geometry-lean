import json
import subprocess
import sys
from pathlib import Path

from tools.infra.hive_multichecker_merge import merge_reports


REPO = Path(__file__).resolve().parents[1]
SCRIPT = REPO / "tools" / "infra" / "hive_multichecker_merge.py"


def write_jsonl(path: Path, rows: list[dict]) -> None:
    path.write_text("\n".join(json.dumps(row) for row in rows) + "\n", encoding="utf-8")


def write_policy(path: Path) -> None:
    path.write_text(
        """
defaults:
  max_soft_failures: 0
  escalate_soft_to_hard_after: 2
  hard_severity_floor: 95
  soft_severity_floor: 70
required_lanes: []
lane_rules: {}
targets: {}
        """.strip()
        + "\n",
        encoding="utf-8",
    )


def write_min_score_policy(path: Path) -> None:
    path.write_text(
        """
defaults:
  max_soft_failures: 1
  escalate_soft_to_hard_after: 2
  hard_severity_floor: 95
  soft_severity_floor: 70
required_lanes: []
lane_rules:
  bee_lean_conductivity:
    required: true
    hard: true
    min_score: 0.75
targets: {}
allowed_axioms: []
forbidden_edge_only_paths: []
        """.strip()
        + "\n",
        encoding="utf-8",
    )


def write_socratic_policy(path: Path) -> None:
    path.write_text(
        """
schema: info_geometry.verification_policy.v1
version: 3
defaults:
  max_soft_failures: 1
  escalate_soft_to_hard_after: 2
  hard_severity_floor: 95
  soft_severity_floor: 70
required_lanes: []
lane_rules:
  bee_kernel_replay:
    required: false
    hard: true
  bee_socratic:
    required: true
    hard: false
targets: {}
allowed_axioms: []
forbidden_edge_only_paths: []
        """.strip()
        + "\n",
        encoding="utf-8",
    )


def test_merge_reports_combines_checker_rows(tmp_path: Path) -> None:
    decls = tmp_path / "decls.jsonl"
    paranoia = tmp_path / "paranoia.jsonl"
    safe = tmp_path / "safe.jsonl"
    auto = tmp_path / "auto.jsonl"
    gate = tmp_path / "gate.json"
    policy = tmp_path / "policy.yaml"
    write_policy(policy)

    write_jsonl(decls, [{"name": "Demo.ok", "module": "Demo", "kind": "theorem"}])
    write_jsonl(paranoia, [{"theorem": "Demo.ok", "success": True, "findings": [], "id": "p1"}])
    write_jsonl(
        safe,
        [
            {
                "declaration": "Demo.ok",
                "success": False,
                "failure_mode": "type mismatch",
                "id": "s1",
            }
        ],
    )
    write_jsonl(
        auto,
        [
            {
                "id": "a1",
                "problems": [
                    {"name": "Demo.ok", "passed": True, "earned": 1, "points": 1},
                    {"name": "Demo.extra", "passed": False, "earned": 0, "points": 2, "message": "bad"},
                ],
            }
        ],
    )
    gate.write_text(json.dumps({"spec_id": "spec", "submission_id": "sub", "promotion_allowed": True, "violations": []}), encoding="utf-8")

    report = merge_reports(
        decl_paths=[decls],
        leanparanoia_path=paranoia,
        safeverify_path=safe,
        autograder_path=auto,
        promotion_path=gate,
        policy_path=policy,
    )

    by_decl = {row["decl"]: row for row in report["declarations"]}
    assert by_decl["Demo.ok"]["ok"] is False
    assert by_decl["Demo.ok"]["tools"]["bee_pauli_policy"]["ok"] is True
    assert by_decl["Demo.ok"]["tools"]["bee_ref_impl"]["ok"] is False
    assert by_decl["Demo.ok"]["score"] == {"earned": 1.0, "total": 1.0}
    assert by_decl["Demo.extra"]["tools"]["bee_autograder"]["ok"] is False
    assert report["summary"]["by_tool"]["bee_ref_impl"]["failed"] >= 1
    assert report["lane_metrics"]["bee_ref_impl"]["tier"] == "tier_a"


def test_merge_contract_rows(tmp_path: Path) -> None:
    decls = tmp_path / "decls.jsonl"
    contract = tmp_path / "contract.jsonl"
    out = tmp_path / "report.json"
    policy = tmp_path / "policy.yaml"
    write_policy(policy)

    write_jsonl(decls, [{"name": "Demo.ok", "module": "Demo", "kind": "theorem"}])
    write_jsonl(
        contract,
        [
            {
                "schema": "info_geometry.verification_result.v1",
                "decl": "Demo.ok",
                "module": "Demo",
                "lane": "bee_kernel_replay",
                "ok": True,
                "severity": 0,
                "checks": ["kernel"],
                "reasons": ["passed"],
            }
        ],
    )
    report = merge_reports(
        decl_paths=[decls],
        leanparanoia_path=contract,
        policy_path=policy,
    )
    assert report["declarations"][0]["tools"]["bee_kernel_replay"]["ok"] is True
    assert report["summary"]["failed_any"] == 0


def test_merge_legacy_source_contract_rows_are_lane_mapped(tmp_path: Path) -> None:
    decls = tmp_path / "decls.jsonl"
    contract = tmp_path / "legacy_contract.jsonl"
    policy = tmp_path / "policy.yaml"
    write_policy(policy)

    write_jsonl(decls, [{"name": "Demo.ok", "module": "Demo", "kind": "theorem"}])
    write_jsonl(
        contract,
        [
            {
                "schema": "info_geometry.verification_result.v1",
                "decl": "Demo.ok",
                "module": "Demo",
                "source": "paperclip",
                "status": "blocked",
                "ok": False,
                "severity": 90,
                "checks": ["paperclip-control"],
                "reasons": ["paperclip blocked"],
            }
        ],
    )

    report = merge_reports(
        decl_paths=[decls],
        leanparanoia_path=contract,
        policy_path=policy,
    )
    assert report["declarations"][0]["tools"]["bee_paperclip"]["ok"] is False
    assert "paperclip blocked" in report["declarations"][0]["tools"]["bee_paperclip"]["error"]


def test_merge_mixed_legacy_source_aliases_are_lane_mapped(tmp_path: Path) -> None:
    decls = tmp_path / "decls.jsonl"
    contracts = tmp_path / "legacy_contracts.jsonl"
    policy = tmp_path / "policy.yaml"
    write_policy(policy)

    write_jsonl(
        decls,
        [
            {"name": "Demo.paperclip", "module": "Demo", "kind": "theorem"},
            {"name": "Demo.paperclip_adapter", "module": "Demo", "kind": "theorem"},
            {"name": "Demo.paperclip_adapter_server", "module": "Demo", "kind": "theorem"},
            {"name": "Demo.hermes_paperclip", "module": "Demo", "kind": "theorem"},
            {"name": "Demo.socratic", "module": "Demo", "kind": "theorem"},
            {"name": "Demo.socratic_question", "module": "Demo", "kind": "theorem"},
        ],
    )
    write_jsonl(
        contracts,
        [
            {
                "schema": "info_geometry.verification_result.v1",
                "decl": "Demo.paperclip",
                "module": "Demo",
                "source": "paperclip",
                "ok": False,
                "severity": 90,
                "checks": ["paperclip-control"],
                "reasons": ["paperclip blocked"],
            },
            {
                "schema": "info_geometry.verification_result.v1",
                "decl": "Demo.paperclip_adapter",
                "module": "Demo",
                "source": "paperclip_adapter",
                "ok": True,
                "severity": 0,
                "checks": ["paperclip-control"],
                "reasons": ["paperclip pass"],
            },
            {
                "schema": "info_geometry.verification_result.v1",
                "decl": "Demo.paperclip_adapter_server",
                "module": "Demo",
                "source": "paperclip_adapter_server",
                "ok": True,
                "severity": 0,
                "checks": ["paperclip-control"],
                "reasons": ["paperclip pass"],
            },
            {
                "schema": "info_geometry.verification_result.v1",
                "decl": "Demo.hermes_paperclip",
                "module": "Demo",
                "source": "hermes_paperclip",
                "ok": True,
                "severity": 0,
                "checks": ["paperclip-control"],
                "reasons": ["paperclip pass"],
            },
            {
                "schema": "info_geometry.verification_result.v1",
                "decl": "Demo.socratic",
                "module": "Demo",
                "source": "socratic",
                "ok": False,
                "severity": 70,
                "checks": ["socratic-question"],
                "reasons": ["status:open"],
            },
            {
                "schema": "info_geometry.verification_result.v1",
                "decl": "Demo.socratic_question",
                "module": "Demo",
                "source": "socratic_question",
                "ok": True,
                "severity": 0,
                "checks": ["socratic-question"],
                "reasons": ["status:resolved"],
            },
        ],
    )

    report = merge_reports(
        decl_paths=[decls],
        lane_contract_paths=[contracts],
        policy_path=policy,
    )
    by_decl = {row["decl"]: row for row in report["declarations"]}
    assert by_decl["Demo.paperclip"]["tools"]["bee_paperclip"]["ok"] is False
    assert by_decl["Demo.paperclip_adapter"]["tools"]["bee_paperclip"]["ok"] is True
    assert by_decl["Demo.paperclip_adapter_server"]["tools"]["bee_paperclip"]["ok"] is True
    assert by_decl["Demo.hermes_paperclip"]["tools"]["bee_paperclip"]["ok"] is True
    assert by_decl["Demo.socratic"]["tools"]["bee_socratic"]["ok"] is False
    assert by_decl["Demo.socratic_question"]["tools"]["bee_socratic"]["ok"] is True


def test_merge_contract_min_score_hard_fail(tmp_path: Path) -> None:
    decls = tmp_path / "decls.jsonl"
    contract = tmp_path / "contract.jsonl"
    policy = tmp_path / "policy.yaml"
    write_min_score_policy(policy)

    write_jsonl(decls, [{"name": "Demo.ok", "module": "Demo", "kind": "theorem"}])
    write_jsonl(
        contract,
        [
            {
                "schema": "info_geometry.verification_result.v1",
                "decl": "Demo.ok",
                "module": "Demo",
                "lane": "bee_lean_conductivity",
                "ok": True,
                "severity": 0,
                "checks": ["conductivity"],
                "reasons": ["passed"],
                "score": {"earned": 6, "total": 10},
            }
        ],
    )
    report = merge_reports(
        decl_paths=[decls],
        lane_contract_paths=[contract],
        policy_path=policy,
    )
    assert report["summary"]["failed_hard"] == 1
    assert report["declarations"][0]["tools"]["bee_lean_conductivity"]["ok"] is False
    assert "score-below-minimum" in report["declarations"][0]["error"]


def test_merge_contract_socratic_soft_and_hard_rules(tmp_path: Path) -> None:
    decls = tmp_path / "decls.jsonl"
    contract = tmp_path / "contract.jsonl"
    policy = tmp_path / "policy.yaml"
    write_socratic_policy(policy)

    write_jsonl(decls, [{"name": "Demo.ok", "module": "Demo", "kind": "theorem"}])
    write_jsonl(
        contract,
        [
            {
                "schema": "info_geometry.verification_result.v1",
                "decl": "Demo.ok",
                "module": "Demo",
                "lane": "bee_socratic",
                "ok": False,
                "severity": 70,
                "checks": ["socratic-question"],
                "reasons": ["status:open"],
            }
        ],
    )

    report = merge_reports(
        decl_paths=[decls],
        lane_contract_paths=[contract],
        policy_path=policy,
    )
    assert report["lane_metrics"]["bee_socratic"]["records"] == 1
    assert report["lane_metrics"]["bee_socratic"]["failed"] == 1
    assert report["lane_metrics"]["bee_socratic"]["decl_health_failed"] == 1
    assert report["declarations"][0]["tools"]["bee_socratic"]["ok"] is False
    assert report["declarations"][0]["ok"] is True
    assert report["declarations"][0]["policy"]["soft_failures"] == 1
    assert report["declarations"][0]["policy"]["hard_failures"] == 0
    assert report["summary"]["failed_soft"] == 0


def write_mixed_lanes_policy(path: Path) -> None:
    path.write_text(
        """
schema: info_geometry.verification_policy.v1
version: 2
defaults:
  max_soft_failures: 0
  escalate_soft_to_hard_after: 2
  hard_severity_floor: 95
  soft_severity_floor: 70
required_lanes:
  - bee_kernel_replay
  - bee_pauli_policy
  - bee_ref_impl
lane_rules:
  bee_kernel_replay:
    required: true
    hard: true
  bee_pauli_policy:
    required: true
    hard: true
  bee_ref_impl:
    required: true
    hard: true
  bee_semantic_guard:
    required: false
    hard: false
        """.strip()
        + "\n",
        encoding="utf-8",
    )


def test_merge_mixed_lanes_end_to_end(tmp_path: Path) -> None:
    decls = tmp_path / "decls.jsonl"
    paranoia = tmp_path / "paranoia.jsonl"
    safe = tmp_path / "safe.jsonl"
    contracts = tmp_path / "lane_contracts.jsonl"
    auto = tmp_path / "auto.jsonl"
    policy = tmp_path / "policy.yaml"
    write_mixed_lanes_policy(policy)

    write_jsonl(
        decls,
        [
            {"name": "Demo.ok", "module": "Demo", "kind": "theorem"},
            {"name": "Demo.missing", "module": "Demo", "kind": "theorem"},
        ],
    )
    write_jsonl(
        paranoia,
        [
            {"theorem": "Demo.ok", "success": True, "findings": [], "id": "p1"},
        ],
    )
    write_jsonl(
        safe,
        [
            {"declaration": "Demo.ok", "success": True, "failure_mode": None, "id": "s1"},
        ],
    )
    write_jsonl(
        contracts,
        [
            {
                "schema": "info_geometry.verification_result.v1",
                "decl": "Demo.ok",
                "module": "Demo",
                "lane": "bee_kernel_replay",
                "ok": True,
                "severity": 0,
                "checks": ["kernel"],
                "reasons": ["passed"],
            },
            {
                "schema": "info_geometry.verification_result.v1",
                "decl": "Demo.missing",
                "module": "Demo",
                "lane": "bee_semantic_guard",
                "ok": False,
                "severity": 80,
                "checks": ["semantic"],
                "reasons": ["classification:block"],
            },
            {
                "schema": "info_geometry.verification_result.v1",
                "decl": "Demo.ok",
                "module": "Demo",
                "lane": "bee_lean_conductivity",
                "ok": True,
                "severity": 0,
                "checks": ["conductivity"],
                "reasons": ["passed"],
            },
        ],
    )
    write_jsonl(
        auto,
        [
            {
                "id": "a1",
                "problems": [
                    {
                        "name": "Demo.ok",
                        "passed": True,
                        "earned": 1,
                        "points": 1,
                        "status": "pass",
                    }
                ],
            }
        ],
    )

    report = merge_reports(
        decl_paths=[decls],
        leanparanoia_path=paranoia,
        safeverify_path=safe,
        autograder_path=auto,
        lane_contract_paths=[contracts],
        policy_path=policy,
    )
    assert report["contract_artifacts"]
    assert report["contract_artifacts"][0]["sha256"] != ""

    by_decl = {row["decl"]: row for row in report["declarations"]}
    assert by_decl["Demo.ok"]["ok"] is True
    assert by_decl["Demo.ok"]["tools"]["bee_kernel_replay"]["ok"] is True
    assert by_decl["Demo.ok"]["tools"]["bee_pauli_policy"]["ok"] is True
    assert by_decl["Demo.ok"]["tools"]["bee_ref_impl"]["ok"] is True
    assert by_decl["Demo.ok"]["error"] is None
    assert by_decl["Demo.missing"]["ok"] is False
    assert by_decl["Demo.missing"]["policy"]["required_missing"] == ["bee_kernel_replay", "bee_pauli_policy", "bee_ref_impl"]
    assert "missing-required-lane" in by_decl["Demo.missing"]["policy"]["lane_decisions"]["bee_pauli_policy"]["reason"]
    assert report["policy"]["lane_tiers"]["bee_kernel_replay"] == "tier_a"
    assert report["lane_metrics"]["bee_kernel_replay"]["records"] == 1
    assert report["lane_metrics"]["bee_kernel_replay"]["decl_health_failed"] == 1
    assert report["lane_health"]["bee_kernel_replay"]["tier"] == "tier_a"


def test_cli_writes_json_and_markdown(tmp_path: Path) -> None:
    decls = tmp_path / "decls.jsonl"
    paranoia = tmp_path / "paranoia.jsonl"
    out = tmp_path / "report.json"
    md = tmp_path / "report.md"
    policy = tmp_path / "policy.yaml"
    write_policy(policy)
    write_jsonl(decls, [{"name": "Demo.ok"}])
    write_jsonl(paranoia, [{"theorem": "Demo.ok", "success": True, "findings": [], "id": "p1"}])

    proc = subprocess.run(
        [
            sys.executable,
            str(SCRIPT),
            "--decls",
            str(decls),
            "--leanparanoia-jsonl",
            str(paranoia),
            "--json-out",
            str(out),
            "--md-out",
            str(md),
            "--policy",
            str(policy),
        ],
        cwd=REPO,
        check=False,
    )

    assert proc.returncode == 0
    report = json.loads(out.read_text(encoding="utf-8"))
    assert report["schema"] == "info_geometry.hive_multichecker_report.v1"
    assert report["summary"]["passed_all"] == 1
    assert "Hive Multi-Checker Report" in md.read_text(encoding="utf-8")
