from __future__ import annotations

import json
import subprocess
from pathlib import Path

from tools.infra import run_superorganism_verification


REPO = Path(__file__).resolve().parents[1]
SCRIPT = REPO / "tools" / "infra" / "run_superorganism_verification.py"


def write_jsonl(path: Path, rows: list[dict]) -> None:
    path.write_text("\n".join(json.dumps(row) for row in rows) + "\n", encoding="utf-8")


def write_policy(path: Path) -> None:
    path.write_text(
        """
schema: info_geometry.verification_policy.v1
version: 2
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


def test_collect_candidate_decl_rows_filters_changed_scope_and_prefix(tmp_path: Path) -> None:
    decl_index = tmp_path / "decls.jsonl"
    write_jsonl(
        decl_index,
        [
            {
                "name": "Demo.ok",
                "module": "Demo",
                "kind": "theorem",
                "file": "/repo/lean/Demo.lean",
            },
            {
                "name": "Demo.skip",
                "module": "Demo",
                "kind": "theorem",
                "file": "/repo/lean/Skip.lean",
            },
            {
                "name": "Other.ok",
                "module": "Other",
                "kind": "theorem",
                "file": "/repo/lean/Other.lean",
            },
        ],
    )

    changed = {Path("/repo/lean/Demo.lean"), Path("/repo/lean/Other.lean")}
    rows = run_superorganism_verification._collect_candidate_decl_rows(
        decl_index=decl_index,
        scope="changed",
        changed_files=changed,
        declaration_prefix=["Demo."],
        max_rows=None,
        root=Path("/repo"),
    )
    assert [row["decl"] for row in rows] == ["Demo.ok"]

    rows = run_superorganism_verification._collect_candidate_decl_rows(
        decl_index=decl_index,
        scope="all",
        changed_files=changed,
        declaration_prefix=[],
        max_rows=2,
        root=Path("/repo"),
    )
    assert len(rows) == 2
    assert rows[0]["decl"] == "Demo.ok"
    assert rows[1]["decl"] == "Demo.skip"


def test_superorganism_pulse_with_no_rows_writes_clean_empty_reports(tmp_path: Path) -> None:
    decl_index = tmp_path / "decls.jsonl"
    policy = tmp_path / "policy.yaml"
    output_root = tmp_path / "verification-runs"
    run_id = "superorganism-empty-run"

    decl_index.write_text(
        "",  # no candidate declarations
        encoding="utf-8",
    )
    write_policy(policy)

    proc = subprocess.run(
        [
            "python3",
            str(SCRIPT),
            "--scope",
            "all",
            "--decl-index",
            str(decl_index),
            "--policy",
            str(policy),
            "--output-root",
            str(output_root),
            "--run-id",
            run_id,
        ],
        cwd=REPO,
        text=True,
        capture_output=True,
        check=False,
    )
    assert proc.returncode == 0, proc.stdout + proc.stderr
    run_dir = output_root / run_id
    payload = json.loads((run_dir / "unified.json").read_text(encoding="utf-8"))
    assert payload["summary"]["total_declarations"] == 0
    assert payload["summary"]["failed_hard"] == 0
    assert payload["summary"]["failed_soft"] == 0
    summary = (run_dir / "summary.md").read_text(encoding="utf-8")
    assert "- status: clean" in summary


def test_superorganism_pulse_appends_pilot_hardening_note(tmp_path: Path) -> None:
    decl_index = tmp_path / "decls.jsonl"
    policy = tmp_path / "policy.yaml"
    output_root = tmp_path / "verification-runs"
    run_id = "superorganism-hardening-note-run"
    payload = tmp_path / "pilot_payload.json"
    summary_note = tmp_path / "pilot_payload_summary.json"

    write_jsonl(
        decl_index,
        [{"name": "Demo.ok", "module": "Demo", "kind": "theorem", "file": "/repo/lean/Demo.lean"}],
    )
    write_policy(policy)
    payload.write_text(
        json.dumps(
            {
                "hard_mode": False,
                "clean_streak": 2,
                "hard_mode_threshold": 4,
                "clean": True,
                "continue_on_error": True,
                "run_id": run_id,
                "policy_path": str(policy),
            },
            sort_keys=True,
        ),
        encoding="utf-8",
    )

    proc = subprocess.run(
        [
            "python3",
            str(SCRIPT),
            "--scope",
            "all",
            "--decl-index",
            str(decl_index),
            "--policy",
            str(policy),
            "--output-root",
            str(output_root),
            "--run-id",
            run_id,
            "--pilot-hardening-payload",
            str(payload),
            "--md-out",
            str(summary_note),
        ],
        cwd=REPO,
        text=True,
        capture_output=True,
        check=False,
    )
    assert proc.returncode == 0, proc.stdout + proc.stderr
    text = summary_note.read_text(encoding="utf-8")
    assert "## Superorganism Pilot Hardening Note" in text
    assert "- hard-mode streak: 2/4" in text
    assert "- streak progress: toward" in text


def test_superorganism_pulse_writes_hardening_note_to_primary_summary_target(tmp_path: Path) -> None:
    decl_index = tmp_path / "decls.jsonl"
    policy = tmp_path / "policy.yaml"
    output_root = tmp_path / "verification-runs"
    run_id = "superorganism-hardening-note-primary-summary"
    payload = tmp_path / "pilot_payload.json"
    primary_summary = tmp_path / "primary_summary.md"

    write_jsonl(
        decl_index,
        [{"name": "Demo.ok", "module": "Demo", "kind": "theorem", "file": "/repo/lean/Demo.lean"}],
    )
    write_policy(policy)
    payload.write_text(
        json.dumps(
            {
                "hard_mode": False,
                "clean_streak": 3,
                "hard_mode_threshold": 4,
                "clean": True,
                "continue_on_error": True,
                "run_id": run_id,
                "policy_path": str(policy),
            },
            sort_keys=True,
        )
        + "\n",
        encoding="utf-8",
    )

    proc = subprocess.run(
        [
            "python3",
            str(SCRIPT),
            "--scope",
            "all",
            "--decl-index",
            str(decl_index),
            "--policy",
            str(policy),
            "--output-root",
            str(output_root),
            "--run-id",
            run_id,
            "--pilot-hardening-payload",
            str(payload),
            "--primary-summary-path",
            str(primary_summary),
        ],
        cwd=REPO,
        text=True,
        capture_output=True,
        check=False,
    )
    assert proc.returncode == 0, proc.stdout + proc.stderr

    run_summary = (output_root / run_id / "summary.md").read_text(encoding="utf-8")
    primary_text = primary_summary.read_text(encoding="utf-8")
    assert "## Superorganism Pilot Hardening Note" in primary_text
    assert "## Superorganism Pilot Hardening Note" not in run_summary
    assert "- hard-mode streak: 3/4" in primary_text


def test_superorganism_pulse_with_pilot_state_updates_single_summary_note_target(tmp_path: Path) -> None:
    decl_index = tmp_path / "decls.jsonl"
    policy = tmp_path / "policy.yaml"
    output_root = tmp_path / "verification-runs"
    run_id = "superorganism-pilot-state-summary-run"
    pilot_state = tmp_path / "superorganism_state.json"
    primary_summary = tmp_path / "primary_summary.md"

    decl_index.write_text("", encoding="utf-8")
    write_policy(policy)
    pilot_state.write_text("{}", encoding="utf-8")

    proc = subprocess.run(
        [
            "python3",
            str(SCRIPT),
            "--scope",
            "all",
            "--decl-index",
            str(decl_index),
            "--policy",
            str(policy),
            "--output-root",
            str(output_root),
            "--run-id",
            run_id,
            "--pilot-state",
            str(pilot_state),
            "--primary-summary-path",
            str(primary_summary),
            "--pilot-hard-mode-threshold",
            "4",
        ],
        cwd=REPO,
        text=True,
        capture_output=True,
        check=False,
    )
    assert proc.returncode == 0, proc.stdout + proc.stderr

    run_summary = (output_root / run_id / "summary.md").read_text(encoding="utf-8")
    primary_text = primary_summary.read_text(encoding="utf-8")
    assert "## Superorganism Pilot Hardening Note" in primary_text
    assert "## Superorganism Pilot Hardening Note" not in run_summary
    assert "- hard-mode streak: 1/4" in primary_text
    assert "- run status: clean" in primary_text

    state = json.loads(pilot_state.read_text(encoding="utf-8"))
    assert "runs" in state
    assert isinstance(state["runs"], list)
    assert state["runs"][-1]["run_id"] == run_id
    assert state["clean_streak"] == 1


def test_superorganism_pulse_with_pilot_state_uses_primary_summary_as_only_note_target(tmp_path: Path) -> None:
    decl_index = tmp_path / "decls.jsonl"
    policy = tmp_path / "policy.yaml"
    output_root = tmp_path / "verification-runs"
    run_id = "superorganism-pilot-state-primary-target"
    pilot_state = tmp_path / "superorganism_state.json"
    primary_summary = tmp_path / "primary_summary.md"

    decl_index.write_text("", encoding="utf-8")
    write_policy(policy)
    pilot_state.write_text("{}", encoding="utf-8")

    proc = subprocess.run(
        [
            "python3",
            str(SCRIPT),
            "--scope",
            "all",
            "--decl-index",
            str(decl_index),
            "--policy",
            str(policy),
            "--output-root",
            str(output_root),
            "--run-id",
            run_id,
            "--pilot-state",
            str(pilot_state),
            "--primary-summary-path",
            str(primary_summary),
            "--pilot-hard-mode-threshold",
            "4",
        ],
        cwd=REPO,
        text=True,
        capture_output=True,
        check=False,
    )
    assert proc.returncode == 0, proc.stdout + proc.stderr

    run_summary = (output_root / run_id / "summary.md").read_text(encoding="utf-8")
    primary_text = primary_summary.read_text(encoding="utf-8")
    assert "## Superorganism Pilot Hardening Note" not in run_summary
    assert primary_text.count("## Superorganism Pilot Hardening Note") == 1


def test_superorganism_pulse_with_pilot_state_single_summary_target_once(tmp_path: Path) -> None:
    decl_index = tmp_path / "decls.jsonl"
    policy = tmp_path / "policy.yaml"
    output_root = tmp_path / "verification-runs"
    run_id = "superorganism-pilot-state-single-target-run"
    pilot_state = tmp_path / "superorganism_state.json"
    primary_summary = tmp_path / "single_target_summary.md"

    decl_index.write_text("", encoding="utf-8")
    write_policy(policy)
    pilot_state.write_text("{}", encoding="utf-8")

    proc = subprocess.run(
        [
            "python3",
            str(SCRIPT),
            "--scope",
            "all",
            "--decl-index",
            str(decl_index),
            "--policy",
            str(policy),
            "--output-root",
            str(output_root),
            "--run-id",
            run_id,
            "--pilot-state",
            str(pilot_state),
            "--primary-summary-path",
            str(primary_summary),
            "--md-out",
            str(primary_summary),
        ],
        cwd=REPO,
        text=True,
        capture_output=True,
        check=False,
    )

    assert proc.returncode == 0, proc.stdout + proc.stderr
    text = primary_summary.read_text(encoding="utf-8")
    assert text.count("## Superorganism Pilot Hardening Note") == 1


def test_superorganism_pulse_with_pilot_state_and_placeholder_signals_single_summary_target(tmp_path: Path) -> None:
    decl_index = tmp_path / "decls.jsonl"
    policy = tmp_path / "policy.yaml"
    output_root = tmp_path / "verification-runs"
    run_id = "superorganism-state-placeholder-signals-single-summary"
    pilot_state = tmp_path / "superorganism_state.json"
    placeholder_report = tmp_path / "placeholder_signals.json"
    primary_summary = tmp_path / "single_target_summary.md"

    decl_index.write_text("", encoding="utf-8")
    write_policy(policy)
    pilot_state.write_text("{}", encoding="utf-8")
    placeholder_report.write_text(
        json.dumps(
            {
                "schema": "info_geometry.placeholder_audit_signals.v1",
                "generated_at": "2026-05-11T00:00:00Z",
                "summary": {
                    "signal_count": 0,
                    "autoproof_signal_count": 0,
                    "closure_debt_signal_count": 0,
                    "finding_count": 0,
                },
                "signals": [],
            },
            sort_keys=True,
        )
        + "\n",
        encoding="utf-8",
    )

    proc = subprocess.run(
        [
            "python3",
            str(SCRIPT),
            "--scope",
            "all",
            "--decl-index",
            str(decl_index),
            "--policy",
            str(policy),
            "--output-root",
            str(output_root),
            "--run-id",
            run_id,
            "--pilot-state",
            str(pilot_state),
            "--primary-summary-path",
            str(primary_summary),
            "--placeholder-signal-report",
            str(placeholder_report),
            "--pilot-hard-mode-threshold",
            "4",
        ],
        cwd=REPO,
        text=True,
        capture_output=True,
        check=False,
    )
    assert proc.returncode == 0, proc.stdout + proc.stderr

    text = primary_summary.read_text(encoding="utf-8")
    assert "## Superorganism Pilot Hardening Note" in text
    assert "## Placeholder Trust Signals" in text
    assert text.count("## Superorganism Pilot Hardening Note") == 1
    assert text.count("## Placeholder Trust Signals") == 1


def test_superorganism_pulse_runs_and_outputs_unified_artifacts(tmp_path: Path) -> None:
    decl_index = tmp_path / "decls.jsonl"
    paranoia = tmp_path / "leanparanoia.jsonl"
    safeverify = tmp_path / "safeverify.jsonl"
    mathfulness = tmp_path / "mathfulness-audit.json"
    conductivity = tmp_path / "conductivity.json"
    policy = tmp_path / "policy.yaml"
    output_root = tmp_path / "verification-runs"
    run_id = "superorganism-test-run"

    write_jsonl(
        decl_index,
        [
            {"name": "Demo.ok", "module": "Demo", "kind": "theorem", "file": "/repo/lean/Demo.lean"},
            {"name": "Demo.blocked", "module": "Demo", "kind": "theorem", "file": "/repo/lean/Demo.lean"},
            {"name": "Other.other", "module": "Other", "kind": "theorem", "file": "/repo/lean/Other.lean"},
        ],
    )
    write_jsonl(
        paranoia,
        [
            {"schema": "info_geometry.leanparanoia_audit.v1", "theorem": "Demo.ok", "success": True, "findings": []},
            {"schema": "info_geometry.leanparanoia_audit.v1", "theorem": "Demo.blocked", "success": False, "findings": []},
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
            },
            {
                "schema": "info_geometry.safeverify_audit.v1",
                "declaration": "Demo.blocked",
                "success": True,
                "failure_mode": None,
            },
        ],
    )
    write_jsonl(
        mathfulness,
        [
            {
                "name": "Demo.blocked",
                "module": "Demo",
                "classification": "blocked",
                "file": "/repo/lean/Demo.lean",
                "line": 1,
            }
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
                        "name": "Demo.blocked",
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
    write_policy(policy)

    proc = subprocess.run(
        [
            "python3",
            str(SCRIPT),
            "--scope",
            "all",
            "--decl-index",
            str(decl_index),
            "--decl-prefix",
            "Demo.",
            "--max-rows",
            "2",
            "--leanparanoia-jsonl",
            str(paranoia),
            "--safeverify-jsonl",
            str(safeverify),
            "--mathfulness-json",
            str(mathfulness),
            "--conductivity-json",
            str(conductivity),
            "--policy",
            str(policy),
            "--output-root",
            str(output_root),
            "--run-id",
            run_id,
        ],
        cwd=REPO,
        text=True,
        capture_output=True,
        check=False,
    )
    assert proc.returncode in (0, 2), proc.stdout + proc.stderr

    run_dir = output_root / run_id
    assert (run_dir / "unified.json").is_file()
    assert (run_dir / "summary.md").is_file()
    payload = json.loads((run_dir / "unified.json").read_text(encoding="utf-8"))
    assert payload["summary"]["total_declarations"] == 2
    assert payload["policy"]["target_class"] == "default"
    assert payload["lane_health"]["bee_pauli_policy"]["records"] == 2
    assert payload["lane_health"]["bee_lean_conductivity"]["records"] == 2


def test_superorganism_changed_scope_passes_base_ref(monkeypatch, tmp_path: Path) -> None:
    decl_index = tmp_path / "decls.jsonl"
    policy = tmp_path / "policy.yaml"
    output_root = tmp_path / "verification-runs"
    run_id = "superorganism-base-ref-run"

    write_jsonl(
        decl_index,
        [{"name": "Demo.ok", "module": "Demo", "kind": "theorem", "file": "/repo/lean/Demo.lean"}],
    )
    write_policy(policy)

    def fake_changed_paths(_root: Path, *, include_untracked: bool, base_ref: str | None) -> set[Path]:
        assert base_ref == "origin/main"
        return {Path("/repo/lean/Demo.lean")}

    def fake_run(_: object) -> int:
        return 0

    monkeypatch.setattr(run_superorganism_verification, "changed_paths", fake_changed_paths)
    monkeypatch.setattr(
        run_superorganism_verification.run_unified_verification,
        "run",
        fake_run,
    )

    ret = run_superorganism_verification.run_pulse(
        run_superorganism_verification.argparse.Namespace(  # type: ignore[attr-defined]
            scope="changed",
            decl_index=decl_index,
            decl_prefix=[],
            max_rows=0,
            include_untracked=False,
            base_ref="origin/main",
            mathfulness_json=None,
            auto_mathfulness=False,
            leanparanoia_jsonl=None,
            safeverify_jsonl=None,
            kernel_jsonl=None,
            autograder_jsonl=None,
            promotion_json=None,
            rethlas_json=None,
            conductivity_json=None,
            socratic_json=None,
            paperclip_json=None,
            policy=policy,
            target_class=None,
            output_root=output_root,
            run_id=run_id,
            json_out=None,
            md_out=None,
            no_lane_wrappers=False,
        )
    )
    assert ret == 0


def test_superorganism_includes_socratic_lane_in_pulse(tmp_path: Path) -> None:
    decl_index = tmp_path / "decls.jsonl"
    socratic = tmp_path / "socratic.jsonl"
    policy = tmp_path / "policy.yaml"
    output_root = tmp_path / "verification-runs"
    run_id = "superorganism-socratic-run"

    write_jsonl(
        decl_index,
        [
            {"name": "Demo.ok", "module": "Demo", "kind": "theorem", "file": "/repo/lean/Demo.lean"},
            {"name": "Demo.skip", "module": "Demo", "kind": "theorem", "file": "/repo/lean/Skip.lean"},
        ],
    )
    write_jsonl(
        socratic,
        [
            {
                "schema": "info_geometry.socratic_packet.v1",
                "kind": "SocraticQuestionPacket",
                "status": "open",
                "question": "Open concern for declaration",
                "target_packet_ids": ["Demo.ok"],
                "question_type": "counterexample_pressure",
            }
        ],
    )
    write_policy(policy)

    proc = subprocess.run(
        [
            "python3",
            str(SCRIPT),
            "--scope",
            "all",
            "--decl-index",
            str(decl_index),
            "--max-rows",
            "2",
            "--socratic-json",
            str(socratic),
            "--policy",
            str(policy),
            "--output-root",
            str(output_root),
            "--run-id",
            run_id,
        ],
        cwd=REPO,
        text=True,
        capture_output=True,
        check=False,
    )
    assert proc.returncode in (0, 2), proc.stdout + proc.stderr

    run_dir = output_root / run_id
    payload = json.loads((run_dir / "unified.json").read_text(encoding="utf-8"))
    assert payload["summary"]["total_declarations"] == 2
    assert payload["lane_health"]["bee_socratic"]["executed"] is True
    assert payload["lane_health"]["bee_socratic"]["records"] == 1
    by_decl = {row["decl"]: row for row in payload["declarations"]}
    assert by_decl["Demo.ok"]["tools"]["bee_socratic"]["ok"] is False


def test_superorganism_includes_paperclip_lane_in_pulse(tmp_path: Path) -> None:
    decl_index = tmp_path / "decls.jsonl"
    paperclip = tmp_path / "paperclip.jsonl"
    policy = tmp_path / "policy.yaml"
    output_root = tmp_path / "verification-runs"
    run_id = "superorganism-paperclip-run"

    write_jsonl(
        decl_index,
        [
            {"name": "Demo.ok", "module": "Demo", "kind": "theorem", "file": "/repo/lean/Demo.lean"},
            {"name": "Demo.skip", "module": "Demo", "kind": "theorem", "file": "/repo/lean/Skip.lean"},
        ],
    )
    write_jsonl(
        paperclip,
        [
            {
                "schema": "info_geometry.paperclip.v1",
                "source": "paperclip",
                "status": "blocked",
                "target_name": "Demo.ok",
            }
        ],
    )
    policy.write_text(
        """
schema: info_geometry.verification_policy.v1
version: 3
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

    proc = subprocess.run(
        [
            "python3",
            str(SCRIPT),
            "--scope",
            "all",
            "--decl-index",
            str(decl_index),
            "--max-rows",
            "2",
            "--paperclip-json",
            str(paperclip),
            "--policy",
            str(policy),
            "--output-root",
            str(output_root),
            "--run-id",
            run_id,
        ],
        cwd=REPO,
        text=True,
        capture_output=True,
        check=False,
    )
    assert proc.returncode in (0, 2), proc.stdout + proc.stderr

    run_dir = output_root / run_id
    payload = json.loads((run_dir / "unified.json").read_text(encoding="utf-8"))
    assert payload["summary"]["total_declarations"] == 2
    assert payload["lane_health"]["bee_paperclip"]["executed"] is True
    assert payload["lane_health"]["bee_paperclip"]["records"] == 1
    by_decl = {row["decl"]: row for row in payload["declarations"]}
    assert by_decl["Demo.ok"]["tools"]["bee_paperclip"]["ok"] is False


def test_superorganism_appends_hardening_note_when_payload_provided(tmp_path: Path) -> None:
    decl_index = tmp_path / "decls.jsonl"
    policy = tmp_path / "policy.yaml"
    output_root = tmp_path / "verification-runs"
    run_id = "superorganism-hardening-note-run"

    write_jsonl(
        decl_index,
        [
            {"name": "Demo.ok", "module": "Demo", "kind": "theorem", "file": "/repo/lean/Demo.lean"},
        ]
    )
    write_policy(policy)

    hard_payload = tmp_path / "hardening_payload.json"
    hard_payload.write_text(
        json.dumps(
            {
                "hard_mode": False,
                "clean_streak": 2,
                "hard_mode_threshold": 4,
                "clean": False,
                "continue_on_error": True,
            }
        )
        + "\n",
        encoding="utf-8",
    )

    proc = subprocess.run(
        [
            "python3",
            str(SCRIPT),
            "--scope",
            "all",
            "--decl-index",
            str(decl_index),
            "--decl-prefix",
            "Demo.",
            "--max-rows",
            "1",
            "--policy",
            str(policy),
            "--output-root",
            str(output_root),
            "--run-id",
            run_id,
            "--pilot-hardening-payload",
            str(hard_payload),
        ],
        cwd=REPO,
        text=True,
        capture_output=True,
        check=False,
    )
    assert proc.returncode in (0, 2), proc.stdout + proc.stderr

    summary = (output_root / run_id / "summary.md").read_text(encoding="utf-8")
    assert "## Superorganism Pilot Hardening Note" in summary
    assert "- run status: failed" in summary
    assert "- hard-mode streak: 2/4" in summary
