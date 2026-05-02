import json
import sys
import types
from pathlib import Path


REPO = Path(__file__).resolve().parents[2]
sys.path.insert(0, str((REPO / "src").resolve()))

from igf import cli as igf_cli


class _StubDB:
    pass


def _invoke_verify(monkeypatch, capsys, verify_payload: dict, argv_extra: list[str] | None = None):
    stub_loader = types.ModuleType("igf.config.loader")
    stub_loader.load_arango_config = lambda: object()

    stub_client = types.ModuleType("igf.graph.arango_client")
    stub_client.connect_db = lambda cfg: _StubDB()

    stub_verify = types.ModuleType("igf.pipeline.verify")
    stub_verify.verify_run = lambda db, run_id, limit=25: dict(verify_payload)

    monkeypatch.setitem(sys.modules, "igf.config.loader", stub_loader)
    monkeypatch.setitem(sys.modules, "igf.graph.arango_client", stub_client)
    monkeypatch.setitem(sys.modules, "igf.pipeline.verify", stub_verify)

    argv = ["verify"]
    if argv_extra:
        argv.extend(argv_extra)
    rc = igf_cli.main(argv)
    out = capsys.readouterr().out.strip()
    return rc, json.loads(out)


def test_verify_cli_success_exit_0_with_required_fields(monkeypatch, capsys) -> None:
    payload = {
        "ok": True,
        "run_id": "run_x",
        "summary": {"run_id": "run_x", "patch_count": 3},
        "orphan_spectral_count": 0,
        "orphan_member_count": 0,
        "orphan_patch_edge_count": 0,
        "policy_violation_count": 0,
        "samples": {
            "orphan_spectral": [],
            "orphan_members": [],
            "orphan_patch_edges": [],
            "policy_violations": [],
        },
    }
    rc, out = _invoke_verify(monkeypatch, capsys, payload, ["--run-id", "run_x", "--limit", "9"])
    assert rc == 0
    assert out["ok"] is True
    for key in [
        "run_id",
        "summary",
        "orphan_spectral_count",
        "orphan_member_count",
        "orphan_patch_edge_count",
        "policy_violation_count",
        "samples",
    ]:
        assert key in out


def test_verify_cli_verdict_failure_exit_2(monkeypatch, capsys) -> None:
    payload = {
        "ok": False,
        "run_id": "run_bad",
        "summary": {"run_id": "run_bad", "patch_count": 3},
        "orphan_spectral_count": 1,
        "orphan_member_count": 0,
        "orphan_patch_edge_count": 0,
        "policy_violation_count": 0,
        "samples": {
            "orphan_spectral": [{"patch_id": "p1"}],
            "orphan_members": [],
            "orphan_patch_edges": [],
            "policy_violations": [],
        },
    }
    rc, out = _invoke_verify(monkeypatch, capsys, payload, ["--run-id", "run_bad"])
    assert rc == 2
    assert out["ok"] is False
    assert out["orphan_spectral_count"] == 1


def test_verify_cli_passes_limit_argument(monkeypatch, capsys) -> None:
    captured = {"limit": None}

    stub_loader = types.ModuleType("igf.config.loader")
    stub_loader.load_arango_config = lambda: object()

    stub_client = types.ModuleType("igf.graph.arango_client")
    stub_client.connect_db = lambda cfg: _StubDB()

    def _verify(db, run_id, limit=25):
        captured["limit"] = limit
        return {
            "ok": True,
            "run_id": run_id or "run_x",
            "summary": {"run_id": run_id or "run_x"},
            "orphan_spectral_count": 0,
            "orphan_member_count": 0,
            "orphan_patch_edge_count": 0,
            "policy_violation_count": 0,
            "samples": {
                "orphan_spectral": [],
                "orphan_members": [],
                "orphan_patch_edges": [],
                "policy_violations": [],
            },
        }

    stub_verify = types.ModuleType("igf.pipeline.verify")
    stub_verify.verify_run = _verify

    monkeypatch.setitem(sys.modules, "igf.config.loader", stub_loader)
    monkeypatch.setitem(sys.modules, "igf.graph.arango_client", stub_client)
    monkeypatch.setitem(sys.modules, "igf.pipeline.verify", stub_verify)

    rc = igf_cli.main(["verify", "--run-id", "run_x", "--limit", "7"])
    _ = capsys.readouterr().out.strip()
    assert rc == 0
    assert captured["limit"] == 7
