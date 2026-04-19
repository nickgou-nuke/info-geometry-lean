import json
import os
import subprocess
from pathlib import Path


REPO = Path(__file__).resolve().parents[1]
WRAPPER = REPO / "tools" / "infra" / "run_gemini_guarded.sh"


def test_guarded_wrapper_check_does_not_record(tmp_path: Path) -> None:
    state = tmp_path / "state.json"
    env = {**os.environ, "PYTHON_BIN": "python3"}

    result = subprocess.run(
        [str(WRAPPER), "--check"],
        cwd=REPO,
        env=env,
        check=True,
        text=True,
        capture_output=True,
    )

    payload = json.loads(result.stdout)
    assert payload["allowed"] is True
    assert not state.exists()


def test_guarded_wrapper_runs_fake_gemini_and_records(tmp_path: Path) -> None:
    fake_bin = tmp_path / "bin"
    fake_bin.mkdir()
    fake_gemini = fake_bin / "gemini"
    fake_gemini.write_text("#!/usr/bin/env bash\necho fake-gemini \"$@\"\n", encoding="utf-8")
    fake_gemini.chmod(0o755)
    state = tmp_path / "state.json"
    env = {
        **os.environ,
        "PATH": f"{fake_bin}:{os.environ['PATH']}",
        "PYTHON_BIN": "python3",
        "GEMINI_GUARD_STATE": str(state),
    }

    result = subprocess.run(
        [str(WRAPPER), "--reason", "unit test", "--", "gemini", "--version"],
        cwd=REPO,
        env=env,
        check=True,
        text=True,
        capture_output=True,
    )

    assert "fake-gemini --version" in result.stdout
    recorded = json.loads(state.read_text(encoding="utf-8"))
    assert len(recorded["events"]) == 1
    assert recorded["events"][0]["reason"] == "unit test"


def test_guarded_wrapper_refuses_non_gemini_command(tmp_path: Path) -> None:
    result = subprocess.run(
        [str(WRAPPER), "--", "echo", "nope"],
        cwd=REPO,
        text=True,
        capture_output=True,
    )

    assert result.returncode == 64
    assert "refusing to run non-gemini command" in result.stderr
