"""Regression: a multi-file `review` runs the staged gate once per index snapshot.

The staged proof gate scans the whole active Git index, independent of the
reviewed file. Running it once per reviewed file made multi-file Gate 4
reviews take minutes per file and amplified index-churn retries.
"""
from __future__ import annotations

import sys
from pathlib import Path
from types import SimpleNamespace
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from tools.infra import opengauss_cli  # noqa: E402
from tools.infra.opengauss_cli import main, review_file  # noqa: E402

_GATE = "tools/quality/proof_proxy_staged_gate.py"


def _fake_repo(tmp_path: Path, index_bytes: bytes = b"index-v1") -> Path:
    (tmp_path / ".git").mkdir()
    (tmp_path / ".git" / "index").write_bytes(index_bytes)
    return tmp_path


def _lean(tmp_path: Path, name: str) -> Path:
    src = tmp_path / name
    src.write_text("theorem t : True := by trivial\n", encoding="utf-8")
    return src


def _gate_calls(run_mock) -> int:
    return sum(1 for c in run_mock.call_args_list if _GATE in c.args[0])


def test_shared_cache_runs_gate_once_for_unchanged_index(tmp_path: Path) -> None:
    repo = _fake_repo(tmp_path)
    files = [_lean(tmp_path, f"F{i}.lean") for i in range(4)]
    cache: dict = {}
    ok = SimpleNamespace(returncode=0, stderr="", stdout="")
    with patch("tools.infra.opengauss_cli.subprocess.run", return_value=ok) as run:
        for f in files:
            review_file(f, gate="GATE_2", repo_root=repo, staged_hook_cache=cache)
    assert _gate_calls(run) == 1


def test_index_change_invalidates_cache(tmp_path: Path) -> None:
    repo = _fake_repo(tmp_path)
    a, b = _lean(tmp_path, "A.lean"), _lean(tmp_path, "B.lean")
    cache: dict = {}
    ok = SimpleNamespace(returncode=0, stderr="", stdout="")
    with patch("tools.infra.opengauss_cli.subprocess.run", return_value=ok) as run:
        review_file(a, gate="GATE_2", repo_root=repo, staged_hook_cache=cache)
        (repo / ".git" / "index").write_bytes(b"index-v2")
        review_file(b, gate="GATE_2", repo_root=repo, staged_hook_cache=cache)
    assert _gate_calls(run) == 2


def test_genuine_finding_is_cached_and_reported_for_every_file(tmp_path: Path) -> None:
    repo = _fake_repo(tmp_path)
    a, b = _lean(tmp_path, "A.lean"), _lean(tmp_path, "B.lean")
    cache: dict = {}
    bad = SimpleNamespace(returncode=1, stderr="missing header", stdout="")
    with patch("tools.infra.opengauss_cli.subprocess.run", return_value=bad) as run:
        reps = [
            review_file(f, gate="GATE_2", repo_root=repo, staged_hook_cache=cache)
            for f in (a, b)
        ]
    assert _gate_calls(run) == 1
    for rep in reps:
        assert any(t["trap_id"] == "QMS_STAGED_HOOK" for t in rep.trap_violations)


def test_churned_result_is_not_cached(tmp_path: Path) -> None:
    repo = _fake_repo(tmp_path)
    a, b = _lean(tmp_path, "A.lean"), _lean(tmp_path, "B.lean")
    cache: dict = {}
    churn = SimpleNamespace(
        returncode=1,
        stderr="active Git index changed during staged proof-proxy scan",
        stdout="",
    )
    with patch("tools.infra.opengauss_cli.subprocess.run", return_value=churn) as run, \
            patch.object(opengauss_cli.time, "sleep"):
        for f in (a, b):
            rep = review_file(f, gate="GATE_2", repo_root=repo, staged_hook_cache=cache)
            assert any(t["trap_id"] == "QMS_STAGED_HOOK_RACY" for t in rep.trap_violations)
    # Three retries per file, no reuse of a churned result.
    assert _gate_calls(run) == 6
    assert cache == {}


def test_without_cache_behaviour_is_unchanged(tmp_path: Path) -> None:
    repo = _fake_repo(tmp_path)
    a, b = _lean(tmp_path, "A.lean"), _lean(tmp_path, "B.lean")
    ok = SimpleNamespace(returncode=0, stderr="", stdout="")
    with patch("tools.infra.opengauss_cli.subprocess.run", return_value=ok) as run:
        review_file(a, gate="GATE_2", repo_root=repo)
        review_file(b, gate="GATE_2", repo_root=repo)
    assert _gate_calls(run) == 2


def test_review_command_shares_cache_across_paths(tmp_path: Path) -> None:
    files = [str(_lean(tmp_path, f"C{i}.lean")) for i in range(3)]
    ok = SimpleNamespace(returncode=0, stderr="", stdout="")
    with patch("tools.infra.opengauss_cli.subprocess.run", return_value=ok) as run, \
            patch.object(opengauss_cli, "_active_index_digest", return_value="same"):
        assert main(["review", *files, "--gate", "GATE_2", "--json"]) == 0
    assert _gate_calls(run) == 1
