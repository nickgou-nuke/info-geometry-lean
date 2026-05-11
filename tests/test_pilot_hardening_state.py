import json
from pathlib import Path

from tools.infra.pilot_hardening_state import (
    action_read,
    action_update,
    build_hardening_note_section,
)


def write_report(path: Path, failed_hard: int = 0, failed_soft: int = 0) -> None:
    path.write_text(
        json.dumps(
            {
                "summary": {
                    "failed_hard": failed_hard,
                    "failed_soft": failed_soft,
                }
            },
            sort_keys=True,
        ),
        encoding="utf-8",
    )


def write_args(path: Path, report: Path | None = None, exit_code: int = 0, action: str = "read") -> object:
    # lightweight namespace substitute for argparse output
    class Namespace:
        pass

    ns = Namespace()
    ns.state = path
    ns.hard_policy_path = "tools/infra/verification_policy_pilot_hard.yaml"
    ns.soft_policy_path = "tools/infra/verification_policy_pilot.yaml"
    ns.hard_mode_threshold = 3
    ns.force_hard = "false"
    ns.action = action
    ns.pilot_report = str(report) if report else ""
    ns.run_id = "run-1"
    ns.exit_code = exit_code
    ns.max_history = 20
    ns.github_output = None
    ns.json_out = None
    ns.markdown_out = None
    return ns


def test_pilot_read_starts_soft(tmp_path: Path) -> None:
    state = tmp_path / "state.json"
    args = write_args(state)
    result = action_read(args)
    assert result["hard_mode"] is False
    assert result["continue_on_error"] is True
    assert result["policy_path"] == "tools/infra/verification_policy_pilot.yaml"
    assert result["clean_streak"] == 0


def test_pilot_update_progresses_streak(tmp_path: Path) -> None:
    state = tmp_path / "state.json"
    report = tmp_path / "pilot.json"
    write_report(report, failed_hard=0, failed_soft=0)
    args = write_args(state, report, exit_code=0, action="update")
    result = action_update(args)
    assert result["clean"] is True
    assert result["clean_streak"] == 1
    assert result["hard_mode"] is False

    args2 = write_args(state, report, exit_code=0, action="update")
    args2.hard_mode_threshold = 1
    result2 = action_update(args2)
    assert result2["clean_streak"] == 2
    assert result2["hard_mode"] is True


def test_pilot_update_writes_json_payload_file(tmp_path: Path) -> None:
    state = tmp_path / "state.json"
    payload = tmp_path / "payload.json"
    report = tmp_path / "pilot.json"
    write_report(report, failed_hard=0, failed_soft=0)
    args = write_args(state, report, exit_code=0, action="update")
    args.hard_mode_threshold = 1
    args.json_out = payload
    result = action_update(args)
    assert result["hard_mode"] is True
    data = json.loads(payload.read_text(encoding="utf-8"))
    assert data["hard_mode"] is True
    assert data["clean_streak"] == 1
    assert data["clean"] is True
    assert data["policy_path"] == "tools/infra/verification_policy_pilot_hard.yaml"


def test_pilot_update_writes_markdown_hardening_note(tmp_path: Path) -> None:
    state = tmp_path / "state.json"
    payload = tmp_path / "payload.json"
    report = tmp_path / "pilot.json"
    summary = tmp_path / "summary.md"
    write_report(report, failed_hard=0, failed_soft=0)
    args = write_args(state, report, exit_code=0, action="update")
    args.hard_mode_threshold = 1
    args.json_out = payload
    args.markdown_out = summary

    result = action_update(args)
    assert result["hard_mode"] is True
    text = summary.read_text(encoding="utf-8")
    assert "## Superorganism Pilot Hardening Note" in text
    assert "- hard-mode streak: 1/1" in text
    assert "- run status: clean" in text


def test_pilot_update_marks_run_id_in_payload_and_note(tmp_path: Path) -> None:
    state = tmp_path / "state.json"
    payload = tmp_path / "payload.json"
    report = tmp_path / "pilot.json"
    summary = tmp_path / "summary.md"
    write_report(report, failed_hard=0, failed_soft=0)
    args = write_args(state, report, exit_code=0, action="update")
    args.hard_mode_threshold = 1
    args.json_out = payload
    args.markdown_out = summary
    args.run_id = "pilot-run-123"

    result = action_update(args)
    assert result["run_id"] == "pilot-run-123"
    data = json.loads(payload.read_text(encoding="utf-8"))
    assert data["run_id"] == "pilot-run-123"
    text = summary.read_text(encoding="utf-8")
    assert "- run id: pilot-run-123" in text


def test_pilot_update_resets_on_failure_and_forces_hard(tmp_path: Path) -> None:
    state = tmp_path / "state.json"
    report_bad = tmp_path / "pilot_bad.json"
    write_report(report_bad, failed_hard=1, failed_soft=0)
    args = write_args(state, report_bad, exit_code=2, action="update")
    args.hard_mode_threshold = 1
    result = action_update(args)
    assert result["clean"] is False
    assert result["clean_streak"] == 0
    assert result["hard_mode"] is False

    args_force = write_args(state, report_bad, exit_code=2, action="update")
    args_force.force_hard = "true"
    args_force.hard_mode_threshold = 1
    result_force = action_update(args_force)
    assert result_force["hard_mode"] is True
    assert result_force["policy_path"] == "tools/infra/verification_policy_pilot_hard.yaml"


def test_hardening_note_marks_streak_progress_toward_for_clean_run() -> None:
    lines = build_hardening_note_section(
        {
            "hard_mode": False,
            "clean_streak": 2,
            "hard_mode_threshold": 4,
            "clean": True,
            "continue_on_error": True,
        }
    )
    assert "- hard-mode streak: 2/4" in lines
    assert "- streak progress: toward" in lines
    assert "- run status: clean" in lines


def test_hardening_note_marks_streak_progress_against_for_failed_run() -> None:
    lines = build_hardening_note_section(
        {
            "hard_mode": False,
            "clean_streak": 0,
            "hard_mode_threshold": 4,
            "clean": False,
            "continue_on_error": True,
        }
    )
    assert "- hard-mode streak: 0/4" in lines
    assert "- streak progress: against" in lines
    assert "- run status: failed" in lines


def test_hardening_note_includes_threshold_line_when_reached() -> None:
    lines = build_hardening_note_section(
        {
            "hard_mode": True,
            "clean_streak": 4,
            "hard_mode_threshold": 4,
            "clean": True,
            "continue_on_error": False,
        }
    )
    assert "- hard-mode threshold reached this run." in lines
