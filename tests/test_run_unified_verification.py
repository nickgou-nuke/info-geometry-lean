from __future__ import annotations

import json
import subprocess
from pathlib import Path

REPO = Path(__file__).resolve().parents[1]
SCRIPT = REPO / "tools" / "infra" / "run_unified_verification.py"


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
allowed_axioms: []
forbidden_edge_only_paths: []
"""
        .strip()
        + "\n",
        encoding="utf-8",
    )


def test_run_unified_verification_writes_archived_artifacts(tmp_path: Path) -> None:
    decls = tmp_path / "decls.jsonl"
    paranoia = tmp_path / "leanparanoia.jsonl"
    safeverify = tmp_path / "safeverify.jsonl"
    policy = tmp_path / "policy.yaml"
    out_root = tmp_path / "reports" / "verification"
    write_policy(policy)

    write_jsonl(decls, [{"name": "Demo.ok", "module": "Demo", "kind": "theorem"}])
    write_jsonl(
        paranoia,
        [
            {
                "schema": "info_geometry.leanparanoia_audit.v1",
                "theorem": "Demo.ok",
                "success": True,
                "findings": [],
                "source_path": "Demo.lean",
                "line": 1,
            }
        ],
    )
    write_jsonl(
        safeverify,
        [
            {
                "schema": "info_geometry.safeverify_audit.v1",
                "declaration": "Demo.ok",
                "success": True,
                "failure_mode": None,
            }
        ],
    )

    result = subprocess.run(
        [
            "python3",
            str(SCRIPT),
            "--decls",
            str(decls),
            "--leanparanoia-jsonl",
            str(paranoia),
            "--safeverify-jsonl",
            str(safeverify),
            "--policy",
            str(policy),
            "--output-root",
            str(out_root),
            "--run-id",
            "manual-test-run",
        ],
        cwd=REPO,
        text=True,
        capture_output=True,
        check=False,
    )
    assert result.returncode == 0, result.stdout + result.stderr

    run_dir = out_root / "manual-test-run"
    assert (run_dir / "unified.json").is_file()
    assert (run_dir / "summary.md").is_file()
    assert (out_root / "latest").is_symlink()
    payload = json.loads((run_dir / "unified.json").read_text(encoding="utf-8"))
    assert payload["summary"]["total_declarations"] == 1
    assert payload["policy"]["hash"] != ""
    assert payload["policy_version"] == payload["policy"]["version"]
    assert payload["policy_hash"] == payload["policy"]["hash"]
    assert payload["contract_schema"] == "info_geometry.verification_result.v1"
    assert payload["contract_version"] == "1"
    assert payload["policy"]["version"] == "1"
    assert payload["policy"]["lane_tiers"]["bee_pauli_policy"] == "tier_b"
    assert payload["lane_metrics"]["bee_ref_impl"]["records"] == 1
    assert "bee_pauli_policy" in payload["lane_health"]
    assert payload["lane_health"]["bee_pauli_policy"]["executed"] is True
    assert payload["lane_health"]["bee_pauli_policy"]["skipped"] is False
    assert payload["lane_health"]["bee_ref_impl"]["executed"] is True
    assert payload["lane_health"]["bee_kernel_replay"]["skipped"] is True
    assert "tier" in payload["lane_health"]["bee_ref_impl"]
    manifest = json.loads((run_dir / "run_manifest.json").read_text(encoding="utf-8"))
    assert manifest["lane_metrics"] == payload["lane_metrics"]
    assert manifest["contract_version"] == payload["contract_version"]
    assert manifest["contract_schema"] == payload["contract_schema"]


def test_run_unified_verification_wires_conductivity_lane(tmp_path: Path) -> None:
    decls = tmp_path / "decls.jsonl"
    conductivity = tmp_path / "conductivity.json"
    policy = tmp_path / "policy.yaml"
    out_root = tmp_path / "reports" / "verification"
    policy.write_text(
        """
schema: info_geometry.verification_policy.v1
version: 2
defaults:
  max_soft_failures: 0
  escalate_soft_to_hard_after: 2
  hard_severity_floor: 95
  soft_severity_floor: 70
lane_rules:
  bee_lean_conductivity:
    required: false
    hard: true
    min_score: 0.7
        """.strip()
        + "\n",
        encoding="utf-8",
    )
    write_jsonl(
        decls,
        [
            {
                "name": "Demo.ok",
                "module": "Demo",
                "kind": "theorem",
            },
            {
                "name": "Demo.fail",
                "module": "Demo",
                "kind": "theorem",
            },
        ],
    )
    write_jsonl(
        conductivity,
        [
            {
                "schema": "info_geometry.representation_depth_from_graph.v1",
                "declarations": [
                    {
                        "name": "Demo.ok",
                        "module": "Demo",
                        "depth": "operator",
                        "targetDepthNat": 2,
                        "directTaggedDepCount": 1,
                        "judgment": "vertical",
                    },
                    {
                        "name": "Demo.fail",
                        "module": "Demo",
                        "depth": "operator",
                        "targetDepthNat": 2,
                        "directTaggedDepCount": 1,
                        "judgment": "wormhole",
                        "reachesAboveClosure": True,
                    },
                ],
            }
        ],
    )

    result = subprocess.run(
        [
            "python3",
            str(SCRIPT),
            "--decls",
            str(decls),
            "--conductivity-json",
            str(conductivity),
            "--policy",
            str(policy),
            "--output-root",
            str(out_root),
            "--run-id",
            "conductivity-run",
        ],
        cwd=REPO,
        text=True,
        capture_output=True,
        check=False,
    )
    assert result.returncode in (0, 2), result.stdout + result.stderr

    payload = json.loads((out_root / "conductivity-run" / "unified.json").read_text(encoding="utf-8"))
    assert payload["summary"]["total_declarations"] == 2
    assert payload["lane_health"]["bee_lean_conductivity"]["executed"] is True
    assert payload["lane_health"]["bee_lean_conductivity"]["records"] == 2
    by_decl = {row["decl"]: row for row in payload["declarations"]}
    assert by_decl["Demo.fail"]["tools"]["bee_lean_conductivity"]["ok"] is False
    assert by_decl["Demo.ok"]["tools"]["bee_lean_conductivity"]["ok"] is True
    assert payload["lane_metrics"]["bee_lean_conductivity"]["records"] == 2


def test_run_unified_verification_runs_socratic_lane(tmp_path: Path) -> None:
    decls = tmp_path / "decls.jsonl"
    sanity = tmp_path / "leanparanoia.jsonl"
    socratic = tmp_path / "socratic.jsonl"
    policy = tmp_path / "policy.yaml"
    out_root = tmp_path / "reports" / "verification"
    policy.write_text(
        """
schema: info_geometry.verification_policy.v1
version: 4
defaults:
  max_soft_failures: 1
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

    write_jsonl(decls, [{"name": "Demo.ok", "module": "Demo", "kind": "theorem"}])
    write_jsonl(
        sanity,
        [
            {
                "schema": "info_geometry.leanparanoia_audit.v1",
                "theorem": "Demo.ok",
                "success": True,
                "findings": [],
            }
        ],
    )
    write_jsonl(
        socratic,
        [
            {
                "schema": "info_geometry.socratic_packet.v1",
                "kind": "SocraticQuestionPacket",
                "status": "open",
                "question": "Can this theorem be closed?",
                "target_packet_ids": ["Demo.ok"],
                "question_type": "missing_hypothesis",
            }
        ],
    )

    result = subprocess.run(
        [
            "python3",
            str(SCRIPT),
            "--decls",
            str(decls),
            "--leanparanoia-jsonl",
            str(sanity),
            "--socratic-json",
            str(socratic),
            "--policy",
            str(policy),
            "--output-root",
            str(out_root),
            "--run-id",
            "socratic-run",
        ],
        cwd=REPO,
        text=True,
        capture_output=True,
        check=False,
    )
    assert result.returncode in (0, 2), result.stdout + result.stderr

    payload = json.loads((out_root / "socratic-run" / "unified.json").read_text(encoding="utf-8"))
    assert payload["lane_health"]["bee_socratic"]["executed"] is True
    assert payload["lane_health"]["bee_socratic"]["records"] == 1
    assert payload["lane_metrics"]["bee_socratic"]["records"] == 1
    assert payload["lane_metrics"]["bee_socratic"]["failed"] == 1
    by_decl = {row["decl"]: row for row in payload["declarations"]}
    assert by_decl["Demo.ok"]["tools"]["bee_socratic"]["ok"] is False


def test_run_unified_verification_runs_paperclip_lane(tmp_path: Path) -> None:
    decls = tmp_path / "decls.jsonl"
    paperclip = tmp_path / "paperclip.jsonl"
    policy = tmp_path / "policy.yaml"
    out_root = tmp_path / "reports" / "verification"
    policy.write_text(
        """
schema: info_geometry.verification_policy.v1
version: 4
defaults:
  max_soft_failures: 1
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

    write_jsonl(decls, [{"name": "Demo.ok", "module": "Demo", "kind": "theorem"}, {"name": "Demo.skip", "module": "Demo", "kind": "theorem"}])
    write_jsonl(
        paperclip,
        [
            {
                "schema": "info_geometry.paperclip.v1",
                "source": "paperclip",
                "status": "blocked",
                "message": "Unresolved control alert",
                "target": {"name": "Demo.ok"},
            },
            {
                "schema": "info_geometry.paperclip.v1",
                "source": "paperclip",
                "status": "running",
                "declaration": "Demo.skip",
            },
        ],
    )

    result = subprocess.run(
        [
            "python3",
            str(SCRIPT),
            "--decls",
            str(decls),
            "--paperclip-json",
            str(paperclip),
            "--policy",
            str(policy),
            "--output-root",
            str(out_root),
            "--run-id",
            "paperclip-run",
        ],
        cwd=REPO,
        text=True,
        capture_output=True,
        check=False,
    )
    assert result.returncode in (0, 2), result.stdout + result.stderr

    payload = json.loads((out_root / "paperclip-run" / "unified.json").read_text(encoding="utf-8"))
    assert payload["summary"]["total_declarations"] == 2
    assert payload["lane_health"]["bee_paperclip"]["executed"] is True
    assert payload["lane_health"]["bee_paperclip"]["records"] == 2
    assert payload["lane_metrics"]["bee_paperclip"]["records"] == 2
    assert payload["lane_metrics"]["bee_paperclip"]["failed"] == 1
    by_decl = {row["decl"]: row for row in payload["declarations"]}
    assert by_decl["Demo.ok"]["tools"]["bee_paperclip"]["ok"] is False
    assert by_decl["Demo.ok"]["policy"]["soft_failures"] == 1
