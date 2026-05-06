import json
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SCRIPT = ROOT / "tools" / "quality" / "kanban_evidence_lint.py"


def run_lint(input_path: Path, *args: str) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        ["python3", str(SCRIPT), "--input", str(input_path), *args],
        cwd=ROOT,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
    )


def test_jsonl_starting_with_object_rows_is_parsed(tmp_path: Path):
    tasks = tmp_path / "tasks.jsonl"
    tasks.write_text(
        "\n".join(
            [
                json.dumps({"task_id": "bad", "state": "done", "summary": "LLM summary"}),
                json.dumps(
                    {
                        "task_id": "good",
                        "state": "verified",
                        "produced_artifacts": {
                            "build_command": "lake env lean lean/InfoGeometry/All.lean",
                            "result": "exit 0",
                        },
                    }
                ),
            ]
        )
        + "\n",
        encoding="utf-8",
    )

    out = tmp_path / "report.json"
    result = run_lint(tasks, "--json-out", str(out))

    assert result.returncode == 0, result.stderr
    report = json.loads(out.read_text(encoding="utf-8"))
    assert report["summary"]["task_count"] == 2
    assert report["summary"]["blocking_finding_count"] == 1
    assert report["summary"]["review_finding_count"] == 1


def test_gate_fails_on_missing_advanced_state_evidence(tmp_path: Path):
    tasks = tmp_path / "tasks.json"
    tasks.write_text(json.dumps([{"task_id": "bad", "state": "promotion_ready"}]), encoding="utf-8")

    result = run_lint(tasks, "--gate")

    assert result.returncode == 1
    assert "promotion_ready requires both build evidence and audit evidence" in result.stdout


def test_gate_passes_with_build_and_audit_evidence(tmp_path: Path):
    tasks = tmp_path / "tasks.json"
    tasks.write_text(
        json.dumps(
            [
                {
                    "task_id": "good",
                    "state": "promotion_ready",
                    "produced_artifacts": {
                        "build_result": "lake build target passed",
                        "audit_report": "reports/dag/semantic-content-audit.json",
                    },
                }
            ]
        ),
        encoding="utf-8",
    )

    result = run_lint(tasks, "--gate")

    assert result.returncode == 0
    report = json.loads(result.stdout)
    assert report["summary"]["blocking_finding_count"] == 0
