import json
import subprocess
import sys
from pathlib import Path

from tools.infra.safeverify_audit_bridge import normalize_safeverify_outcome


REPO = Path(__file__).resolve().parents[1]
SCRIPT = REPO / "tools" / "infra" / "safeverify_audit_bridge.py"


def test_normalize_safeverify_success_outcome() -> None:
    row = normalize_safeverify_outcome(
        {
            "targetInfo": {"constInfo": {"kind": "theorem"}, "axioms": ["propext"]},
            "solutionInfo": {"constInfo": {"kind": "theorem"}, "axioms": ["propext"]},
            "failureMode": None,
        },
        target_olean="target.olean",
        submission_olean="submission.olean",
    )

    assert row["schema"] == "info_geometry.safeverify_audit.v1"
    assert row["success"] is True
    assert row["target_kind"] == "theorem"
    assert row["solution_axioms"] == ["propext"]
    assert row["authority"]["lean_remains_proof_authority"] is True


def test_normalize_safeverify_failure_outcome() -> None:
    row = normalize_safeverify_outcome(
        {
            "targetInfo": {"constInfo": {"kind": "theorem"}, "axioms": []},
            "solutionInfo": None,
            "failureMode": "declaration not found in submission",
        }
    )

    assert row["success"] is False
    assert row["failure_mode"] == "declaration not found in submission"


def test_cli_normalizes_existing_json_report(tmp_path: Path) -> None:
    report = tmp_path / "safeverify.json"
    out = tmp_path / "out"
    report.write_text(
        json.dumps(
            [
                {
                    "targetInfo": {"constInfo": {"kind": "theorem"}, "axioms": ["Classical.choice"]},
                    "solutionInfo": {"constInfo": {"kind": "theorem"}, "axioms": ["Classical.choice"]},
                    "failureMode": None,
                },
                {
                    "targetInfo": {"constInfo": {"kind": "def"}, "axioms": []},
                    "solutionInfo": {"constInfo": {"kind": "theorem"}, "axioms": []},
                    "failureMode": "kind mismatch (expected def, got theorem)",
                },
            ]
        ),
        encoding="utf-8",
    )

    proc = subprocess.run(
        [
            sys.executable,
            str(SCRIPT),
            "--input",
            str(report),
            "--output-dir",
            str(out),
        ],
        cwd=REPO,
        check=False,
    )

    assert proc.returncode == 2
    rows = (out / "safeverify_audit.jsonl").read_text(encoding="utf-8").splitlines()
    summary = json.loads((out / "safeverify_audit_summary.json").read_text(encoding="utf-8"))
    assert len(rows) == 2
    assert summary["successes"] == 1
    assert summary["failures"] == 1
