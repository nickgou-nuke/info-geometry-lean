from __future__ import annotations

import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SCRIPT = ROOT / "tools" / "infra" / "ask_repo.py"


def run(*args: str) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        ["python3", str(SCRIPT), *args],
        cwd=ROOT,
        text=True,
        capture_output=True,
        check=False,
    )


def test_ask_repo_no_gravity_smoke() -> None:
    proc = run("Weyl character formula", "--no-gravity", "--top-k", "3")
    assert proc.returncode == 0, proc.stderr
    stdout = proc.stdout.lower()
    assert "graphrag explorer" in stdout
    assert "lean declarations" in stdout
    assert "docs / black books / handover" in stdout


def test_ask_repo_json_mode() -> None:
    proc = run("Weyl character formula", "--no-gravity", "--top-k", "3", "--format", "json")
    assert proc.returncode == 0, proc.stderr
    assert proc.stdout.strip().startswith("{")
