from __future__ import annotations

import argparse
import os
import subprocess
import sys
from pathlib import Path

import pytest

REPO = Path(__file__).resolve().parents[2]
SCRIPT = REPO / "tools" / "infra" / "research_digest_worker.py"


def test_research_digest_worker_resolves_8532_under_poisoned_generic_env() -> None:
    env = os.environ.copy()
    env["PYTHONPATH"] = f"{REPO}:{REPO / 'src'}"
    env["ARANGO_ENDPOINT"] = "http://127.0.0.1:8530"
    env["ARANGO_DATABASE"] = "infogeometry"
    env["HIVE_ARANGO_ENDPOINT"] = "http://127.0.0.1:8540"
    env["HIVE_ARANGO_DB"] = "hive_live"
    for key in ("ALEXANDRIA_ARANGO_ENDPOINT", "ALEXANDRIA_ARANGO_DB", "ALEXANDRIA_DATABASE"):
        env.pop(key, None)

    code = (
        "import json, tools.infra.research_digest_worker as rdw; "
        "print(json.dumps({'endpoint': rdw.ALEX_ENDPOINT, 'database': rdw.ALEX_DATABASE}))"
    )
    proc = subprocess.run(
        [sys.executable, "-c", code],
        cwd=REPO,
        env=env,
        capture_output=True,
        text=True,
        check=True,
    )
    assert '"endpoint": "http://127.0.0.1:8532"' in proc.stdout
    assert '"database": "alexandria"' in proc.stdout


def test_research_digest_worker_guard_blocks_forbidden_targets(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    saved_env = dict(os.environ)
    try:
        import tools.infra.research_digest_worker as rdw
    finally:
        for k in list(os.environ):
            if k not in saved_env:
                os.environ.pop(k, None)
        os.environ.update(saved_env)

    spawned: list[str] = []
    monkeypatch.setattr(rdw, "BASE_DIR", tmp_path)
    monkeypatch.setattr(rdw, "shell", lambda cmd, timeout: (spawned.append(cmd) or 0, "ok"))

    goal = {"_key": "goal_1", "module": "TestMod", "target_pretty": "See arXiv:2401.12345"}
    task = {"_key": "task_1"}

    for bad_ep, bad_db in (
        ("http://127.0.0.1:8530", "alexandria"),
        ("http://127.0.0.1:8540", "alexandria"),
        ("http://127.0.0.1:8532", "infogeometry"),
        ("http://127.0.0.1:8532", "hive_live"),
    ):
        args = argparse.Namespace(
            timeout=30,
            alexandria_endpoint=bad_ep,
            alexandria_database=bad_db,
            alexandria_username="root",
            alexandria_password="pw",
        )
        with pytest.raises(ValueError):
            rdw.process_task(args, task, goal)
    assert spawned == []

    # Valid :8532 target succeeds and quotes args cleanly
    good_args = argparse.Namespace(
        timeout=30,
        alexandria_endpoint="http://127.0.0.1:8532",
        alexandria_database="alexandria",
        alexandria_username="root",
        alexandria_password="p w",
    )
    out = rdw.process_task(good_args, task, goal)
    assert out["arxiv_ids"] == ["2401.12345"]
    assert len(spawned) == 1
    assert "--endpoint http://127.0.0.1:8532 --database alexandria" in spawned[0]
    assert "--password 'p w'" in spawned[0]


def test_research_digest_worker_cli_rejects_8530_on_startup() -> None:
    env = os.environ.copy()
    env["PYTHONPATH"] = f"{REPO}:{REPO / 'src'}"
    proc = subprocess.run(
        [
            sys.executable,
            str(SCRIPT),
            "--once",
            "--alexandria-endpoint",
            "http://127.0.0.1:8530",
        ],
        cwd=REPO,
        env=env,
        capture_output=True,
        text=True,
    )
    assert proc.returncode == 2


def test_research_digest_worker_empty_endpoint_and_unreachable_hive(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    import tools.infra.research_digest_worker as rdw

    with pytest.raises(ValueError, match="empty"):
        rdw._resolve_alexandria_target(
            argparse.Namespace(
                alexandria_endpoint="",
                alexandria_database="alexandria",
                alexandria_username="root",
                alexandria_password="pw",
            )
        )

    env = os.environ.copy()
    env["PYTHONPATH"] = f"{REPO}:{REPO / 'src'}"
    proc = subprocess.run(
        [sys.executable, str(SCRIPT), "--once", "--hive-endpoint", "http://127.0.0.1:59999"],
        cwd=REPO,
        env=env,
        capture_output=True,
        text=True,
    )
    assert proc.returncode == 1
    assert "Traceback" not in proc.stderr
