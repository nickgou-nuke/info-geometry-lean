from __future__ import annotations

import subprocess
from pathlib import Path

from tools.infra import build_changed_lean


def test_changed_paths_uses_merge_base(monkeypatch: object) -> None:
    calls: list[list[str]] = []

    def fake_run_git(args: list[str], cwd: Path) -> list[str]:
        calls.append(list(args))
        if args == ["merge-base", "origin/main", "HEAD"]:
            return ["abc123"]
        if args == ["diff", "--name-only", "abc123"]:
            return ["lean/Foo.lean"]
        if args[:3] == ["diff", "--cached", "--name-only"]:
            return []
        if args == ["ls-files", "--others", "--exclude-standard"]:
            return []
        raise AssertionError(f"unexpected git args: {args}")

    monkeypatch.setattr(build_changed_lean, "run_git", fake_run_git)
    paths = build_changed_lean.changed_paths(Path("/repo"), include_untracked=False, base_ref="origin/main")

    assert len(calls) >= 2
    assert calls[0] == ["merge-base", "origin/main", "HEAD"]
    assert calls[1] == ["diff", "--name-only", "abc123"]
    assert Path("/repo/lean/Foo.lean").resolve() in paths


def test_changed_paths_falls_back_to_head(monkeypatch: object) -> None:
    calls: list[list[str]] = []

    def fake_run_git(args: list[str], cwd: Path) -> list[str]:
        calls.append(list(args))
        if args == ["merge-base", "origin/main", "HEAD"]:
            raise subprocess.CalledProcessError(returncode=1, cmd=args)
        if args == ["diff", "--name-only", "HEAD"]:
            return ["lean/Bar.lean"]
        if args[:3] == ["diff", "--cached", "--name-only"]:
            return []
        if args == ["ls-files", "--others", "--exclude-standard"]:
            return []
        raise AssertionError(f"unexpected git args: {args}")

    monkeypatch.setattr(build_changed_lean, "run_git", fake_run_git)
    paths = build_changed_lean.changed_paths(Path("/repo"), include_untracked=False, base_ref="origin/main")

    assert calls[0] == ["merge-base", "origin/main", "HEAD"]
    assert calls[1] == ["diff", "--name-only", "HEAD"]
    assert Path("/repo/lean/Bar.lean").resolve() in paths
