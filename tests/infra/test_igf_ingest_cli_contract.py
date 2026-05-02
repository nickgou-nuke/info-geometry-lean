import json
import sys
import types
from pathlib import Path


REPO = Path(__file__).resolve().parents[2]
sys.path.insert(0, str((REPO / "src").resolve()))

from igf import cli as igf_cli


class _StubDB:
    pass


def _invoke_ingest(monkeypatch, capsys, ingest_payload: dict, argv_extra: list[str] | None = None):
    stub_loader = types.ModuleType("igf.config.loader")
    stub_loader.load_arango_config = lambda: object()

    stub_client = types.ModuleType("igf.graph.arango_client")
    stub_client.connect_db = lambda cfg: _StubDB()

    stub_ingest = types.ModuleType("igf.pipeline.ingest")
    stub_ingest.ingest_artifacts = lambda db, dir_path: dict(ingest_payload)

    monkeypatch.setitem(sys.modules, "igf.config.loader", stub_loader)
    monkeypatch.setitem(sys.modules, "igf.graph.arango_client", stub_client)
    monkeypatch.setitem(sys.modules, "igf.pipeline.ingest", stub_ingest)

    argv = ["ingest"]
    if argv_extra:
        argv.extend(argv_extra)
    rc = igf_cli.main(argv)
    out = capsys.readouterr().out.strip()
    return rc, json.loads(out)


def test_ingest_cli_success_exit_0(monkeypatch, capsys) -> None:
    payload = {
        "ok": True,
        "run_id": "run_ingest_ok",
        "counts": {"ig_chiral_patches": 3},
    }
    rc, out = _invoke_ingest(monkeypatch, capsys, payload, ["--dir", "some/dir"])
    assert rc == 0
    assert out["ok"] is True
    assert out["run_id"] == "run_ingest_ok"


def test_ingest_cli_failure_exit_1(monkeypatch, capsys) -> None:
    payload = {
        "ok": False,
        "error": "connection_failed",
    }
    rc, out = _invoke_ingest(monkeypatch, capsys, payload)
    assert rc == 1
    assert out["ok"] is False
    assert out["error"] == "connection_failed"
