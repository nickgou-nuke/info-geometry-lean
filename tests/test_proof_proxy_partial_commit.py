"""Regression tests: the staged gate's checker/index consistency under partial commits."""

from __future__ import annotations

import os
import subprocess
from pathlib import Path

import pytest

from tools.quality.proof_proxy_staged_gate import EXECUTED_GATE_SOURCES, checker_index_mismatches


def _git(repo: Path, *args: str, env: dict[str, str] | None = None) -> None:
    subprocess.run(["git", *args], cwd=repo, check=True, capture_output=True, env=env)


@pytest.fixture()
def repo(tmp_path: Path) -> Path:
    _git(tmp_path, "init", "-q")
    _git(tmp_path, "config", "user.email", "test@example.invalid")
    _git(tmp_path, "config", "user.name", "test")
    for rel in EXECUTED_GATE_SOURCES:
        path = tmp_path / rel
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text("# v1\n", encoding="utf-8")
    _git(tmp_path, "add", "-A")
    _git(tmp_path, "commit", "-q", "-m", "init")
    return tmp_path


def _temporary_head_index(repo: Path) -> dict[str, str]:
    """Mimic `git commit --only`: a temporary index built from HEAD."""
    env = dict(os.environ)
    env["GIT_INDEX_FILE"] = str(repo / ".git" / "tmp-only-index")
    _git(repo, "read-tree", "HEAD", env=env)
    return env


def test_staged_checker_edit_passes_under_partial_commit(repo: Path, monkeypatch) -> None:
    checker = repo / EXECUTED_GATE_SOURCES[1]
    checker.write_text("# v2 staged\n", encoding="utf-8")
    _git(repo, "add", EXECUTED_GATE_SOURCES[1])
    env = _temporary_head_index(repo)
    monkeypatch.setenv("GIT_INDEX_FILE", env["GIT_INDEX_FILE"])
    assert checker_index_mismatches(repo) == []


def test_unstaged_checker_edit_still_fails_under_partial_commit(repo: Path, monkeypatch) -> None:
    checker = repo / EXECUTED_GATE_SOURCES[1]
    checker.write_text("# v2 unstaged\n", encoding="utf-8")
    env = _temporary_head_index(repo)
    monkeypatch.setenv("GIT_INDEX_FILE", env["GIT_INDEX_FILE"])
    assert checker_index_mismatches(repo) == [EXECUTED_GATE_SOURCES[1]]


def test_unstaged_checker_edit_fails_in_normal_commit(repo: Path, monkeypatch) -> None:
    monkeypatch.delenv("GIT_INDEX_FILE", raising=False)
    checker = repo / EXECUTED_GATE_SOURCES[0]
    checker.write_text("# v2 unstaged\n", encoding="utf-8")
    assert checker_index_mismatches(repo) == [EXECUTED_GATE_SOURCES[0]]
