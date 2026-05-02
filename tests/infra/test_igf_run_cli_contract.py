import json
import sys
import types
from pathlib import Path


REPO = Path(__file__).resolve().parents[2]
sys.path.insert(0, str((REPO / "src").resolve()))

from igf import cli as igf_cli


def _run_with_stubbed_orchestrator(monkeypatch, payload: dict):
    stub = types.ModuleType("igf.pipeline.orchestrator")

    def run_offline_pipeline(**kwargs):
        return dict(payload)

    stub.run_offline_pipeline = run_offline_pipeline
    monkeypatch.setitem(sys.modules, "igf.pipeline.orchestrator", stub)

    rc = igf_cli.main(["run", "--verify"])
    return rc


def test_igf_run_cli_returns_0_on_success(monkeypatch, capsys) -> None:
    rc = _run_with_stubbed_orchestrator(
        monkeypatch,
        {"ok": True, "stage": "complete", "exit_code": 0},
    )
    assert rc == 0
    out = capsys.readouterr().out.strip()
    payload = json.loads(out)
    assert payload["ok"] is True
    assert payload["exit_code"] == 0


def test_igf_run_cli_returns_1_on_runtime_failure(monkeypatch, capsys) -> None:
    rc = _run_with_stubbed_orchestrator(
        monkeypatch,
        {"ok": False, "stage": "ingest", "exit_code": 1},
    )
    assert rc == 1
    out = capsys.readouterr().out.strip()
    payload = json.loads(out)
    assert payload["ok"] is False
    assert payload["exit_code"] == 1


def test_igf_run_cli_returns_2_on_verify_verdict_failure(monkeypatch, capsys) -> None:
    rc = _run_with_stubbed_orchestrator(
        monkeypatch,
        {"ok": False, "stage": "verify", "exit_code": 2},
    )
    assert rc == 2
    out = capsys.readouterr().out.strip()
    payload = json.loads(out)
    assert payload["ok"] is False
    assert payload["exit_code"] == 2
