import json
import subprocess
import sys
from pathlib import Path

from tools.infra.hive_workflow_policy import check_workflow_policy, declaration_header


REPO = Path(__file__).resolve().parents[1]
SCRIPT = REPO / "tools" / "infra" / "hive_workflow_policy.py"


def test_declaration_header_ignores_body_changes() -> None:
    before = "theorem Demo.good (x : Nat) : x = x := by rfl"
    after = "theorem Demo.good (x : Nat) : x = x := by\n  exact rfl"

    assert declaration_header(before) == declaration_header(after)


def test_prove_mode_rejects_header_change() -> None:
    report = check_workflow_policy(
        mode="prove",
        before_files={"Demo.lean": "theorem Demo.good : True := by trivial"},
        after_files={"Demo.lean": "theorem Demo.good : True := by exact True.intro"},
        theorem_before="theorem Demo.good : True := by trivial",
        theorem_after="theorem Demo.good : False := by contradiction",
        allow_unsound_markers=True,
    )

    assert report["ok"] is False
    assert report["guards"]["header_immutable"] is True
    assert {v["code"] for v in report["violations"]} == {"declaration_header_changed"}


def test_formalize_mode_allows_header_change() -> None:
    report = check_workflow_policy(
        mode="formalize",
        before_files={"Demo.lean": "theorem Demo.good : True := by trivial"},
        after_files={"Demo.lean": "theorem Demo.good : False := by contradiction"},
        theorem_before="theorem Demo.good : True := by trivial",
        theorem_after="theorem Demo.good : False := by contradiction",
        allow_unsound_markers=True,
    )

    assert report["ok"] is True
    assert report["guards"]["header_immutable"] is False


def test_review_mode_is_read_only() -> None:
    report = check_workflow_policy(
        mode="review",
        before_files={"Demo.lean": "def x := 1"},
        after_files={"Demo.lean": "def x := 2"},
        allow_unsound_markers=True,
    )

    assert report["ok"] is False
    assert report["violations"][0]["code"] == "no_edit_mode_modified_files"


def test_checkpoint_requires_build_and_axiom_gates() -> None:
    report = check_workflow_policy(
        mode="checkpoint",
        before_files={},
        after_files={},
        targeted_build_passed=True,
        project_build_passed=False,
        axiom_audit_passed=False,
    )

    assert report["ok"] is False
    assert {v["code"] for v in report["violations"]} == {
        "checkpoint_missing_project_build",
        "checkpoint_missing_axiom_audit",
    }


def test_unsound_markers_are_rejected_by_default() -> None:
    report = check_workflow_policy(
        mode="draft",
        before_files={},
        after_files={"Demo.lean": "theorem Demo.bad : True := by sorry"},
    )

    assert report["ok"] is False
    assert report["violations"][0]["code"] == "unsound_marker_present"


def test_cli_writes_report_and_returns_nonzero_on_violation(tmp_path: Path) -> None:
    before = tmp_path / "before.json"
    after = tmp_path / "after.json"
    out = tmp_path / "report.json"
    before.write_text(json.dumps({"Demo.lean": "def x := 1"}), encoding="utf-8")
    after.write_text(json.dumps({"Demo.lean": "def x := 2"}), encoding="utf-8")

    proc = subprocess.run(
        [
            sys.executable,
            str(SCRIPT),
            "--mode",
            "review",
            "--before-files-json",
            str(before),
            "--after-files-json",
            str(after),
            "--json-out",
            str(out),
        ],
        cwd=REPO,
        check=False,
    )

    assert proc.returncode == 2
    report = json.loads(out.read_text(encoding="utf-8"))
    assert report["schema"] == "info_geometry.hive_workflow_policy.v1"
    assert report["violations"][0]["code"] == "no_edit_mode_modified_files"
