from __future__ import annotations

from pathlib import Path
from types import SimpleNamespace
from typing import Any

import pytest

from tools.infra.pantograph_environment import (
    build_environment_manifest,
    manifest_fingerprint,
    verify_environment_match,
)


def test_environment_manifest_fingerprints_source_lock_oleans_and_pantograph_tree(tmp_path: Path) -> None:
    root = tmp_path / "project"
    source = root / "lean" / "Example.lean"
    target_olean = root / ".lake/build/lib/lean/Example.olean"
    imported_olean = root / ".lake/packages/mathlib/.lake/build/lib/lean/Mathlib/Core.olean"
    lean_lib = tmp_path / "toolchain/lib/lean"
    repl_root = root / "external_refs/Pantograph"
    executable = repl_root / ".lake/build/bin/repl"
    for path in (source, target_olean, imported_olean, lean_lib / "Init.olean"):
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(path.name.encode())
    (root / "lean-toolchain").write_text("leanprover/lean4:v4.34.1\n", encoding="utf-8")
    (root / "lakefile.lean").write_text("package test\n", encoding="utf-8")
    (root / "lake-manifest.json").write_text("{\"packages\":[]}\n", encoding="utf-8")
    (repl_root / ".git").mkdir(parents=True)
    (repl_root / "Repl.lean").write_text("def repl := 1\n", encoding="utf-8")
    executable.parent.mkdir(parents=True)
    executable.write_bytes(b"repl executable")

    def runner(args: list[str], *, cwd: Path, **_kwargs: Any) -> Any:
        if args[:3] == ["lake", "env", "lean"] and "--deps" in args:
            stdout = f"{imported_olean}\n{lean_lib / 'Init.olean'}\n"
        elif args[:3] == ["lake", "env", "lean"] and "--print-libdir" in args:
            stdout = str(lean_lib)
        elif args[:3] == ["lake", "env", "lean"] and "--version" in args:
            stdout = "Lean (version 4.34.1)"
        elif args == ["lake", "--version"]:
            stdout = "Lake version 5"
        elif args[:3] == ["git", "rev-parse", "HEAD"]:
            stdout = "pantograph-head"
        elif args[:2] == ["git", "ls-files"]:
            stdout = "Repl.lean\0"
        else:
            raise AssertionError((args, cwd))
        return SimpleNamespace(returncode=0, stdout=stdout, stderr="")

    command = [str(executable), "Example"]
    manifest = build_environment_manifest(root, source, command, runner=runner)
    assert manifest["fingerprint"] == manifest_fingerprint(manifest)
    assert manifest["pantograph"]["gitHead"] == "pantograph-head"
    assert manifest["startupModules"] == ["Example"]
    assert len(manifest["leanOleans"]) == 3  # import, core import, and target module

    imported_olean.write_bytes(b"changed imported artifact")
    changed = build_environment_manifest(root, source, command, runner=runner)
    assert changed["fingerprint"] != manifest["fingerprint"]
    with pytest.raises(RuntimeError, match="differ"):
        verify_environment_match(manifest, changed)


def test_environment_fingerprint_detects_manifest_tampering() -> None:
    # Fingerprint checking is independent of Arango persistence and canonical JSON ordering.
    first = {"schema": "test", "inputs": {"b": 2, "a": 1}}
    first["fingerprint"] = manifest_fingerprint(first)
    assert manifest_fingerprint(first) == first["fingerprint"]
    first["inputs"]["a"] = 9
    assert manifest_fingerprint(first) != first["fingerprint"]
