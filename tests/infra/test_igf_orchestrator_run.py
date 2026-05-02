from pathlib import Path
import sys


REPO = Path(__file__).resolve().parents[2]
sys.path.insert(0, str((REPO / "src").resolve()))

from igf.pipeline import orchestrator


def test_run_offline_pipeline_returns_exit_1_on_build_failure(monkeypatch):
    monkeypatch.setattr(orchestrator, "build_chiral_patches", lambda **kwargs: {"ok": False, "error": "boom"})

    result = orchestrator.run_offline_pipeline(
        nodes=Path("n.jsonl"),
        edges=Path("e.jsonl"),
        fingerprints=None,
        output_dir=Path("out"),
        schemas_dir=Path("schemas"),
        run_id="run_x",
        strict=True,
    )

    assert result["ok"] is False
    assert result["stage"] == "build"
    assert result["exit_code"] == 1


def test_run_offline_pipeline_returns_exit_2_on_verify_verdict_failure(monkeypatch):
    monkeypatch.setattr(orchestrator, "build_chiral_patches", lambda **kwargs: {"ok": True, "run_id": "run_x"})
    monkeypatch.setattr(orchestrator, "validate_artifacts", lambda *args, **kwargs: {"ok": True})
    monkeypatch.setattr(orchestrator, "load_arango_config", lambda: object())
    monkeypatch.setattr(orchestrator, "connect_db", lambda cfg: object())
    monkeypatch.setattr(orchestrator, "ingest_artifacts", lambda db, artifact_dir: {"ok": True})
    monkeypatch.setattr(
        orchestrator,
        "verify_run",
        lambda db, run_id, limit=25: {"ok": False, "run_id": "run_x", "policy_violation_count": 1},
    )

    result = orchestrator.run_offline_pipeline(
        nodes=Path("n.jsonl"),
        edges=Path("e.jsonl"),
        fingerprints=None,
        output_dir=Path("out"),
        schemas_dir=Path("schemas"),
        run_id="run_x",
        strict=True,
        do_ingest=True,
        do_verify=True,
        verify_limit=10,
    )

    assert result["ok"] is False
    assert result["stage"] == "verify"
    assert result["exit_code"] == 2


def test_run_offline_pipeline_full_success_exit_0(monkeypatch):
    monkeypatch.setattr(orchestrator, "build_chiral_patches", lambda **kwargs: {"ok": True, "run_id": "run_x"})
    monkeypatch.setattr(orchestrator, "validate_artifacts", lambda *args, **kwargs: {"ok": True})
    monkeypatch.setattr(orchestrator, "load_arango_config", lambda: object())
    monkeypatch.setattr(orchestrator, "connect_db", lambda cfg: object())
    monkeypatch.setattr(orchestrator, "ingest_artifacts", lambda db, artifact_dir: {"ok": True, "ingested": {}})
    monkeypatch.setattr(orchestrator, "verify_run", lambda db, run_id, limit=25: {"ok": True, "run_id": "run_x"})

    result = orchestrator.run_offline_pipeline(
        nodes=Path("n.jsonl"),
        edges=Path("e.jsonl"),
        fingerprints=None,
        output_dir=Path("out"),
        schemas_dir=Path("schemas"),
        run_id="run_x",
        strict=True,
        do_ingest=True,
        do_verify=True,
        verify_limit=10,
    )

    assert result["ok"] is True
    assert result["stage"] == "complete"
    assert result["exit_code"] == 0
