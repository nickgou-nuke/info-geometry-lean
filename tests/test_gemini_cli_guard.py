import json
import subprocess
import sys
from pathlib import Path


REPO = Path(__file__).resolve().parents[1]
TOOL = REPO / "tools" / "infra" / "gemini_cli_guard.py"


def run_guard(state: Path, *args: str) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        [sys.executable, str(TOOL), "--state", str(state), *args],
        text=True,
        capture_output=True,
    )


def test_gemini_guard_records_then_blocks_until_interval(tmp_path: Path) -> None:
    state = tmp_path / "gemini-state.json"

    first = run_guard(state, "--json", "--reason", "operator test")
    assert first.returncode == 0
    first_payload = json.loads(first.stdout)
    assert first_payload["allowed"] is True

    second = run_guard(state, "--json")
    assert second.returncode == 2
    second_payload = json.loads(second.stdout)
    assert second_payload["allowed"] is False
    assert "dream interval" in second_payload["reason"]

    recorded = json.loads(state.read_text())
    assert recorded["policy"]["explicit_operator_only"] is True
    assert recorded["policy"]["auto_route"] is False
    assert recorded["policy"]["mode"] == "irregular_dreaming_sidecar"
    assert len(recorded["events"]) == 1


def test_gemini_guard_check_does_not_record(tmp_path: Path) -> None:
    state = tmp_path / "gemini-state.json"

    check = run_guard(state, "--check", "--json")
    assert check.returncode == 0
    assert json.loads(check.stdout)["allowed"] is True
    assert not state.exists()


def test_gemini_guard_daily_cap_is_enforced(tmp_path: Path) -> None:
    state = tmp_path / "gemini-state.json"

    first = run_guard(
        state,
        "--json",
        "--now",
        "1000",
        "--min-interval-seconds",
        "0",
        "--jitter-seconds",
        "0",
        "--max-calls-per-day",
        "1",
    )
    assert first.returncode == 0

    second = run_guard(
        state,
        "--json",
        "--now",
        "1001",
        "--min-interval-seconds",
        "0",
        "--jitter-seconds",
        "0",
        "--max-calls-per-day",
        "1",
    )
    assert second.returncode == 2
    payload = json.loads(second.stdout)
    assert payload["allowed"] is False
    assert "daily Gemini CLI limit" in payload["reason"]


def test_gemini_guard_fails_closed_on_corrupt_state(tmp_path: Path) -> None:
    state = tmp_path / "gemini-state.json"
    state.write_text("{not-json", encoding="utf-8")

    result = run_guard(state, "--json")

    assert result.returncode == 2
    payload = json.loads(result.stdout)
    assert payload["allowed"] is False
    assert "invalid guard state" in payload["reason"]
