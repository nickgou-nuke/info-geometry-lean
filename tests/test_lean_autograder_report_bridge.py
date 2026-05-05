import json
import subprocess
import sys
from pathlib import Path

from tools.infra.lean_autograder_report_bridge import normalize_autograder_payload


REPO = Path(__file__).resolve().parents[1]
SCRIPT = REPO / "tools" / "infra" / "lean_autograder_report_bridge.py"


def test_normalize_autograder_payload_scores_problem_rows() -> None:
    row = normalize_autograder_payload(
        {
            "problems": [
                {"name": "th1", "kind": "proof", "passed": True, "earned": 1, "points": 1},
                {"name": "reverse", "kind": "def", "passed": False, "earned": 0, "points": 2, "message": "not equal"},
            ]
        },
        Path("autograder.json"),
    )

    assert row["schema"] == "info_geometry.lean_autograder_report.v1"
    assert row["passed"] is False
    assert row["problem_count"] == 2
    assert row["passed_count"] == 1
    assert row["failed_count"] == 1
    assert row["earned_points"] == 1
    assert row["total_points"] == 3
    assert row["authority"]["lean_remains_proof_authority"] is True


def test_cli_normalizes_existing_autograder_json(tmp_path: Path) -> None:
    report = tmp_path / "autograder.json"
    out = tmp_path / "out"
    report.write_text(
        json.dumps(
            {
                "results": [
                    {"problem": "goal", "type": "proof", "status": "passed", "score": 1, "points": 1},
                ]
            }
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

    assert proc.returncode == 0
    rows = (out / "lean_autograder_report.jsonl").read_text(encoding="utf-8").splitlines()
    summary = json.loads((out / "lean_autograder_report_summary.json").read_text(encoding="utf-8"))
    assert len(rows) == 1
    assert summary["passed_count"] == 1
