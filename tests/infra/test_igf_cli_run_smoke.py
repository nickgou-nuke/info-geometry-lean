import shutil
import subprocess
import sys
from pathlib import Path


REPO = Path(__file__).resolve().parents[2]
CLI = REPO / "cli" / "igf.py"
PYTHON = shutil.which("python3") or sys.executable


def test_cli_run_help_lists_new_flags() -> None:
    result = subprocess.run(
        [PYTHON, str(CLI), "run", "--help"],
        text=True,
        capture_output=True,
        check=False,
        cwd=str(REPO),
    )
    assert result.returncode == 0
    out = result.stdout
    assert "--ingest" in out
    assert "--verify" in out
    assert "--verify-limit" in out
    assert "--schemas-dir" in out


def test_cli_run_rejects_invalid_verify_limit_type() -> None:
    result = subprocess.run(
        [PYTHON, str(CLI), "run", "--verify-limit", "not-an-int"],
        text=True,
        capture_output=True,
        check=False,
        cwd=str(REPO),
    )
    assert result.returncode != 0
    assert "invalid int value" in result.stderr
