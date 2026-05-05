import json
import subprocess
import sys
from pathlib import Path

from tools.infra.hive_spec_submission_policy import (
    make_submission_packet,
    make_target_spec_packet,
    promotion_gate,
    validate_spec_submission_pair,
)


REPO = Path(__file__).resolve().parents[1]
SCRIPT = REPO / "tools" / "infra" / "hive_spec_submission_policy.py"


def test_target_spec_and_submission_packets_match_expected_declarations() -> None:
    spec = make_target_spec_packet(
        spec_id="demo",
        target_file="Target.lean",
        target_source="def solveAdd (a b : Int) : Int := sorry\ntheorem solveAdd_spec : True := by sorry",
    )
    submission = make_submission_packet(
        spec_id="demo",
        submission_id="sub1",
        submission_file="Submission.lean",
        submission_source="def solveAdd (a b : Int) : Int := b - a\ntheorem solveAdd_spec : True := by trivial",
    )

    assert spec["expected_declarations"] == ["solveAdd", "solveAdd_spec"]
    assert submission["declared_declarations"] == ["solveAdd", "solveAdd_spec"]
    assert validate_spec_submission_pair(spec, submission) == []


def test_submission_with_unsound_marker_blocks_pair() -> None:
    spec = make_target_spec_packet(
        spec_id="demo",
        target_file="Target.lean",
        target_source="theorem goal : True := by sorry",
    )
    submission = make_submission_packet(
        spec_id="demo",
        submission_id="bad",
        submission_file="Submission.lean",
        submission_source="theorem goal : True := by sorry",
    )

    codes = {v["code"] for v in validate_spec_submission_pair(spec, submission)}
    assert "submission_unsound_markers" in codes


def test_promotion_gate_requires_build_paranoia_and_safeverify() -> None:
    spec = make_target_spec_packet(
        spec_id="demo",
        target_file="Target.lean",
        target_source="theorem goal : True := by sorry",
        expected_declarations=["goal"],
    )
    submission = make_submission_packet(
        spec_id="demo",
        submission_id="sub1",
        submission_file="Submission.lean",
        submission_source="theorem goal : True := by trivial",
    )

    gate = promotion_gate(
        spec=spec,
        submission=submission,
        build_passed=True,
        leanparanoia_rows=[{"id": "lp1", "success": True}],
        safeverify_rows=[{"id": "sv1", "success": True}],
    )

    assert gate["promotion_allowed"] is True
    assert gate["authority"] == "audit_checked"


def test_promotion_gate_rejects_failed_safeverify() -> None:
    spec = make_target_spec_packet(
        spec_id="demo",
        target_file="Target.lean",
        target_source="theorem goal : True := by sorry",
        expected_declarations=["goal"],
    )
    submission = make_submission_packet(
        spec_id="demo",
        submission_id="sub1",
        submission_file="Submission.lean",
        submission_source="theorem goal : True := by trivial",
    )

    gate = promotion_gate(
        spec=spec,
        submission=submission,
        build_passed=True,
        leanparanoia_rows=[{"id": "lp1", "success": True}],
        safeverify_rows=[{"id": "sv1", "success": False}],
    )

    assert gate["promotion_allowed"] is False
    assert {v["code"] for v in gate["violations"]} == {"safeverify_failed"}


def test_promotion_gate_records_autograder_points_and_rejects_failure() -> None:
    spec = make_target_spec_packet(
        spec_id="demo",
        target_file="Target.lean",
        target_source="theorem goal : True := by sorry",
        expected_declarations=["goal"],
    )
    submission = make_submission_packet(
        spec_id="demo",
        submission_id="sub1",
        submission_file="Submission.lean",
        submission_source="theorem goal : True := by trivial",
    )

    gate = promotion_gate(
        spec=spec,
        submission=submission,
        build_passed=True,
        leanparanoia_rows=[{"id": "lp1", "success": True}],
        safeverify_rows=[{"id": "sv1", "success": True}],
        autograder_rows=[{"id": "ag1", "passed": False, "earned_points": 1, "total_points": 2}],
    )

    assert gate["promotion_allowed"] is False
    assert gate["autograder_points"] == {"earned": 1.0, "total": 2.0}
    assert {v["code"] for v in gate["violations"]} == {"autograder_failed"}


def test_cli_builds_packets_and_gate(tmp_path: Path) -> None:
    target = tmp_path / "Target.lean"
    submission_file = tmp_path / "Submission.lean"
    spec_packet = tmp_path / "spec.json"
    submission_packet = tmp_path / "submission.json"
    paranoia = tmp_path / "leanparanoia.jsonl"
    safeverify = tmp_path / "safeverify.jsonl"
    gate = tmp_path / "gate.json"
    target.write_text("theorem goal : True := by sorry\n", encoding="utf-8")
    submission_file.write_text("theorem goal : True := by trivial\n", encoding="utf-8")
    paranoia.write_text(json.dumps({"id": "lp", "success": True}) + "\n", encoding="utf-8")
    safeverify.write_text(json.dumps({"id": "sv", "success": True}) + "\n", encoding="utf-8")

    subprocess.run(
        [
            sys.executable,
            str(SCRIPT),
            "target-spec",
            "--spec-id",
            "demo",
            "--target-file",
            str(target),
            "--out",
            str(spec_packet),
        ],
        cwd=REPO,
        check=True,
    )
    subprocess.run(
        [
            sys.executable,
            str(SCRIPT),
            "submission",
            "--spec-id",
            "demo",
            "--submission-id",
            "sub1",
            "--submission-file",
            str(submission_file),
            "--out",
            str(submission_packet),
        ],
        cwd=REPO,
        check=True,
    )
    proc = subprocess.run(
        [
            sys.executable,
            str(SCRIPT),
            "promotion-gate",
            "--spec-packet",
            str(spec_packet),
            "--submission-packet",
            str(submission_packet),
            "--build-passed",
            "--leanparanoia-jsonl",
            str(paranoia),
            "--safeverify-jsonl",
            str(safeverify),
            "--out",
            str(gate),
        ],
        cwd=REPO,
        check=False,
    )

    assert proc.returncode == 0
    gate_payload = json.loads(gate.read_text(encoding="utf-8"))
    assert gate_payload["promotion_allowed"] is True
