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


def test_is_import_only_umbrella_and_skip_by_default(tmp_path: Path, monkeypatch: object) -> None:
    modular = tmp_path / "lean" / "InfoGeometry" / "Modular.lean"
    owner = tmp_path / "lean" / "InfoGeometry" / "Canonical" / "Owner.lean"
    stub = tmp_path / "lean" / "InfoGeometry" / "Canonical" / "Stub.lean"
    modular.parent.mkdir(parents=True)
    owner.parent.mkdir(parents=True)
    modular.write_text(
        "/- copyright /- nested -/ -/\n-- note\nimport InfoGeometry.Modular.A\npublic import InfoGeometry.Modular.B\n",
        encoding="utf-8",
    )
    owner.write_text("import InfoGeometry.Modular\ndef val : Nat := 1\n", encoding="utf-8")
    stub.write_text("-- modified stub\n", encoding="utf-8")

    assert build_changed_lean.is_import_only_umbrella(modular) is True
    assert build_changed_lean.is_import_only_umbrella(owner) is False
    assert build_changed_lean.is_import_only_umbrella(stub) is False

    monkeypatch.setattr(
        build_changed_lean,
        "changed_paths",
        lambda root, **kwargs: {modular.resolve(), owner.resolve(), stub.resolve()},
    )

    default_mods = build_changed_lean.collect_modules(
        tmp_path,
        include_untracked=True,
        allow_umbrella=False,
        prefix="InfoGeometry.",
        source_root="lean",
    )
    assert default_mods == ["InfoGeometry.Canonical.Owner", "InfoGeometry.Canonical.Stub"]

    with_umbrella = build_changed_lean.collect_modules(
        tmp_path,
        include_untracked=True,
        allow_umbrella=True,
        prefix="InfoGeometry.",
        source_root="lean",
    )
    assert "InfoGeometry.Modular" in with_umbrella


def test_collect_modules_respects_scope_paths(tmp_path: Path, monkeypatch: object) -> None:
    target = tmp_path / "lean" / "InfoGeometry" / "Canonical" / "Target.lean"
    other = tmp_path / "lean" / "InfoGeometry" / "Other" / "Noise.lean"
    target.parent.mkdir(parents=True)
    other.parent.mkdir(parents=True)
    target.write_text("def x : Nat := 0\n", encoding="utf-8")
    other.write_text("def y : Nat := 0\n", encoding="utf-8")

    monkeypatch.setattr(
        build_changed_lean,
        "changed_paths",
        lambda root, **kwargs: {target.resolve(), other.resolve()},
    )

    scoped_file = build_changed_lean.collect_modules(
        tmp_path,
        include_untracked=True,
        allow_umbrella=False,
        prefix="InfoGeometry.",
        source_root="lean",
        scope_paths=[Path("lean/InfoGeometry/Canonical/Target.lean")],
    )
    assert scoped_file == ["InfoGeometry.Canonical.Target"]

    scoped_dir = build_changed_lean.collect_modules(
        tmp_path,
        include_untracked=True,
        allow_umbrella=False,
        prefix="InfoGeometry.",
        source_root="lean",
        scope_paths=[Path("lean/InfoGeometry/Canonical")],
    )
    assert scoped_dir == ["InfoGeometry.Canonical.Target"]


def test_changed_paths_staged_only_ignores_unstaged_and_untracked(monkeypatch: object) -> None:
    calls: list[list[str]] = []

    def fake_run_git(args: list[str], cwd: Path) -> list[str]:
        calls.append(list(args))
        if args == ["diff", "--cached", "--name-only", "HEAD"]:
            return ["lean/Staged.lean"]
        raise AssertionError(f"unexpected git args in staged_only mode: {args}")

    monkeypatch.setattr(build_changed_lean, "run_git", fake_run_git)
    paths = build_changed_lean.changed_paths(Path("/repo"), include_untracked=True, staged_only=True)

    assert calls == [["diff", "--cached", "--name-only", "HEAD"]]
    assert paths == {Path("/repo/lean/Staged.lean").resolve()}


def test_default_source_root_is_lean_only(monkeypatch: object) -> None:
    monkeypatch.setattr("sys.argv", ["build_changed_lean.py"])
    args = build_changed_lean.parse_args()
    assert args.source_root == "auto"
    assert build_changed_lean._selected_lanes(Path("/repo"), args.source_root, None) == ("lean",)
    assert build_changed_lean._selected_lanes(
        Path("/repo"), args.source_root, [Path("src/Foo.lean")]
    ) == ("src",)
