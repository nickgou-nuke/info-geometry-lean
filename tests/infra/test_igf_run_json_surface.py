import json
import sys
import types
from pathlib import Path


REPO = Path(__file__).resolve().parents[2]
sys.path.insert(0, str((REPO / "src").resolve()))

from igf import cli as igf_cli


def _invoke_run(monkeypatch, capsys, payload: dict, extra_args: list[str] | None = None):
    stub = types.ModuleType("igf.pipeline.orchestrator")

    def run_offline_pipeline(**kwargs):
        return dict(payload)

    stub.run_offline_pipeline = run_offline_pipeline
    monkeypatch.setitem(sys.modules, "igf.pipeline.orchestrator", stub)

    argv = ["run"]
    if extra_args:
        argv.extend(extra_args)
    rc = igf_cli.main(argv)
    out = capsys.readouterr().out.strip()
    return rc, json.loads(out)


def test_run_json_surface_build_failure_has_minimal_keys(monkeypatch, capsys) -> None:
    rc, payload = _invoke_run(
        monkeypatch,
        capsys,
        {
            "ok": False,
            "stage": "build",
            "exit_code": 1,
            "build": {"ok": False, "error": "boom"},
        },
    )

    assert rc == 1
    assert payload["ok"] is False
    assert payload["stage"] == "build"
    assert payload["exit_code"] == 1
    assert "build" in payload
    assert "validate" not in payload
    assert "ingest" not in payload
    assert "verify" not in payload


def test_run_json_surface_validate_failure_has_build_and_validate(monkeypatch, capsys) -> None:
    rc, payload = _invoke_run(
        monkeypatch,
        capsys,
        {
            "ok": False,
            "stage": "validate",
            "exit_code": 1,
            "build": {"ok": True, "run_id": "run_x"},
            "validate": {"ok": False, "error_count": 2},
        },
    )

    assert rc == 1
    assert payload["stage"] == "validate"
    assert "build" in payload
    assert "validate" in payload
    assert "ingest" not in payload
    assert "verify" not in payload


def test_run_json_surface_verify_failure_has_all_stages(monkeypatch, capsys) -> None:
    rc, payload = _invoke_run(
        monkeypatch,
        capsys,
        {
            "ok": False,
            "stage": "verify",
            "exit_code": 2,
            "build": {"ok": True, "run_id": "run_x"},
            "validate": {"ok": True},
            "ingest": {"ok": True, "ingested": {}},
            "verify": {"ok": False, "policy_violation_count": 1},
        },
        extra_args=["--verify"],
    )

    assert rc == 2
    assert payload["stage"] == "verify"
    assert "build" in payload
    assert "validate" in payload
    assert "ingest" in payload
    assert "verify" in payload


def test_run_json_surface_success_with_verify_has_all_stages(monkeypatch, capsys) -> None:
    rc, payload = _invoke_run(
        monkeypatch,
        capsys,
        {
            "ok": True,
            "stage": "complete",
            "exit_code": 0,
            "build": {"ok": True, "run_id": "run_x"},
            "validate": {"ok": True},
            "ingest": {"ok": True, "ingested": {}},
            "verify": {"ok": True, "run_id": "run_x"},
        },
        extra_args=["--verify", "--verify-limit", "7"],
    )

    assert rc == 0
    assert payload["ok"] is True
    assert payload["stage"] == "complete"
    assert payload["exit_code"] == 0
    assert "build" in payload
    assert "validate" in payload
    assert "ingest" in payload
    assert "verify" in payload
