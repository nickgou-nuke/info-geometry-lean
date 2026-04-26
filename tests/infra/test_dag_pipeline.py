import json
import subprocess
import sys
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[2]
TOOLS_INFRA = REPO_ROOT / "tools" / "infra"


def run_script(script_name, *args):
    return subprocess.run(
        [sys.executable, str(TOOLS_INFRA / script_name), *map(str, args)],
        cwd=REPO_ROOT,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )


def assert_valid_empty_json(path: Path):
    assert path.exists()
    data = json.loads(path.read_text())

    # Keep these assertions schema-tolerant unless the project has a fixed schema.
    serialized = json.dumps(data).lower()
    assert "error" not in serialized

    if "findings" in data:
        assert data["findings"] == []

    if "summary" in data:
        numeric_values = [
            value for key, value in data["summary"].items()
            if isinstance(value, int) and "version" not in key.lower() and "iterations" not in key.lower()
        ]
        assert all(value == 0 for value in numeric_values)


def test_process_flow_report_allows_missing_inputs(tmp_path):
    input_dir = tmp_path / "missing-process-flow"
    output_json = tmp_path / "process-flow-report.json"
    output_md = tmp_path / "process-flow-report.md"

    result = run_script(
        "generate_process_flow_report.py",
        "--input-dir", input_dir,
        "--json-out", output_json,
        "--report-out", output_md,
        "--allow-missing-input",
    )

    assert result.returncode == 0, result.stderr
    assert_valid_empty_json(output_json)
    assert output_md.exists()
    assert "clean" in output_md.read_text().lower()


def test_process_flow_report_fails_without_allow_missing_input(tmp_path):
    input_dir = tmp_path / "missing-process-flow"
    output_json = tmp_path / "process-flow-report.json"
    output_md = tmp_path / "process-flow-report.md"

    result = run_script(
        "generate_process_flow_report.py",
        "--input-dir", input_dir,
        "--json-out", output_json,
        "--report-out", output_md,
    )

    assert result.returncode != 0


def test_semantic_flow_report_allows_missing_inputs(tmp_path):
    input_dir = tmp_path / "missing-semantic-flow"
    output_json = tmp_path / "semantic-flow-report.json"
    output_md = tmp_path / "semantic-flow-report.md"

    result = run_script(
        "generate_semantic_flow_report.py",
        "--input-dir", input_dir,
        "--json-out", output_json,
        "--md-out", output_md,
        "--allow-missing-input",
    )

    assert result.returncode == 0, result.stderr
    assert_valid_empty_json(output_json)
    assert output_md.exists()
    assert "clean" in output_md.read_text().lower()


def test_semantic_flow_check_allows_missing_report(tmp_path):
    report_json = tmp_path / "missing-semantic-flow-report.json"

    result = run_script(
        "check_semantic_flow_report.py",
        "--json-out", report_json,
        "--allow-missing-input",
    )

    assert result.returncode == 0, result.stderr


def test_semantic_flow_check_fails_without_allow_missing_input(tmp_path):
    report_json = tmp_path / "missing-semantic-flow-report.json"

    result = run_script(
        "check_semantic_flow_report.py",
        "--json-out", report_json,
    )

    assert result.returncode != 0
