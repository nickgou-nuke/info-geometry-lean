"""Regression tests for items 1-6 incremental pipeline hardening."""

from __future__ import annotations

import json
import subprocess
import tempfile
from pathlib import Path
from types import SimpleNamespace
from unittest.mock import patch

import pytest

from tools.build_lock import BuildLock, BuildLockBusyError
from tools.infra import axiom_audit, axiom_index, build_changed_lean, opengauss_screener, run_locked_lean
from tools.quality import proof_proxy_staged_gate as gate


def _git(repo: Path, *args: str) -> str:
    return subprocess.run(
        ["git", *args], cwd=repo, check=True, capture_output=True, text=True
    ).stdout


def _init_repo(tmp_path: Path, monkeypatch) -> Path:
    _git(tmp_path, "init", "-q")
    _git(tmp_path, "config", "user.email", "test@example.invalid")
    _git(tmp_path, "config", "user.name", "Test")
    base = tmp_path / "base.txt"
    base.write_text("base\n", encoding="utf-8")
    _git(tmp_path, "add", "base.txt")
    _git(tmp_path, "commit", "-qm", "init")
    monkeypatch.chdir(tmp_path)
    return tmp_path


# --- 1. BuildLock LOCK_SH / LOCK_EX ----------------------------------------


def test_build_lock_allows_concurrent_readers_and_blocks_writers(tmp_path: Path) -> None:
    lock_path = tmp_path / "rw.lock"
    writer_init = BuildLock(lock_path, "initial-writer").acquire()
    writer_init.release()
    assert lock_path.read_text(encoding="utf-8") == ""

    r1 = BuildLock(lock_path, "reader-1", block=False, shared=True).acquire()
    try:
        r2 = BuildLock(lock_path, "reader-2", block=False, shared=True).acquire()
        try:
            with pytest.raises(BuildLockBusyError):
                BuildLock(lock_path, "blocked-writer", block=False, shared=False).acquire()
        finally:
            r2.release()
    finally:
        r1.release()

    writer = BuildLock(lock_path, "active-writer", block=False, shared=False).acquire()
    try:
        payload = json.loads(lock_path.read_text(encoding="utf-8"))
        assert payload["owner"] == "active-writer"
        with pytest.raises(BuildLockBusyError):
            BuildLock(lock_path, "blocked-reader", block=False, shared=True).acquire()
    finally:
        writer.release()


# --- 2. run_locked_lean cached LEAN_PATH & batch shared checks --------------


def test_resolve_cached_lean_env_hits_cache_and_invalidates_on_toolchain_edit(tmp_path: Path) -> None:
    (tmp_path / "lean-toolchain").write_text("leanprover/lean4:v4.34.1\n", encoding="utf-8")
    (tmp_path / "lakefile.lean").write_text("package demo\n", encoding="utf-8")
    fake_lean = tmp_path / "fake_lean"
    fake_leanc = tmp_path / "fake_leanc"
    fake_lean.write_text("#!/bin/sh\n", encoding="utf-8")
    fake_leanc.write_text("#!/bin/sh\n", encoding="utf-8")

    probe_payload = json.dumps({
        "lean": str(fake_lean),
        "leanc": str(fake_leanc),
        "LEAN_PATH": "/tmp/lean_path",
        "LEAN_SRC_PATH": "",
        "LD_LIBRARY_PATH": "",
        "PATH": "/usr/bin",
    })
    with patch.object(
        run_locked_lean.subprocess,
        "run",
        return_value=SimpleNamespace(returncode=0, stdout=probe_payload + "\n", stderr=""),
    ) as sub_run:
        first = run_locked_lean.resolve_cached_lean_env(tmp_path)
        assert first is not None and first["LEAN_PATH"] == "/tmp/lean_path"
        assert sub_run.call_count == 1

        second = run_locked_lean.resolve_cached_lean_env(tmp_path)
        assert second == first
        assert sub_run.call_count == 1  # pure cache hit

        (tmp_path / "lean-toolchain").write_text("leanprover/lean4:v4.35.0\n", encoding="utf-8")
        third = run_locked_lean.resolve_cached_lean_env(tmp_path)
        assert third is not None
        assert sub_run.call_count == 2  # invalidated cleanly


def test_writes_artifacts_selects_shared_vs_exclusive_lock(tmp_path: Path) -> None:
    assert run_locked_lean._writes_artifacts(["--json"], run_script=False) is False
    assert run_locked_lean._writes_artifacts(["-o", "out.olean"], run_script=False) is True
    assert run_locked_lean._writes_artifacts(["--c=out.c"], run_script=False) is True
    assert run_locked_lean._writes_artifacts(["-o", "ignored"], run_script=True) is False

    a = tmp_path / "A.lean"
    b = tmp_path / "B.lean"
    a.write_text("theorem a : True := trivial\n", encoding="utf-8")
    b.write_text("theorem b : True := trivial\n", encoding="utf-8")

    observed_locks: list[bool] = []

    class DummyLock:
        def release(self) -> None:
            return None

    def fake_acquire(_path, _owner, *, block=True, shared=False):
        del block
        observed_locks.append(shared)
        return DummyLock()

    with (
        patch.object(run_locked_lean, "_validate_lake_workspace_integrity", return_value=None),
        patch.object(run_locked_lean, "acquire_build_lock", side_effect=fake_acquire),
        patch.object(run_locked_lean, "resolve_cached_lean_env", return_value=None),
        patch.object(
            run_locked_lean.subprocess,
            "run",
            return_value=SimpleNamespace(returncode=0),
        ) as sub_run,
    ):
        rc = run_locked_lean.execute_locked_lean_batch([a, b], root=tmp_path, verbose=False)
        assert rc == 0
        assert observed_locks == [True]  # one shared lock for the entire batch
        assert sub_run.call_count == 2

        run_locked_lean.execute_locked_lean(a, ["-o", "A.olean"], root=tmp_path)
        assert observed_locks[-1] is False  # exclusive lock when writing artifacts


# --- 3. axiom_index single-batch scanning ----------------------------------


def test_axiom_index_batches_modules_into_one_fast_invocation(tmp_path: Path) -> None:
    olean_dir = tmp_path / ".lake" / "build" / "lib" / "lean"
    p1 = olean_dir / "InfoGeometry" / "ModA.olean"
    p2 = olean_dir / "InfoGeometry" / "ModB.olean"
    p1.parent.mkdir(parents=True)
    p1.write_bytes(b"olean1")
    p2.write_bytes(b"olean2")
    lock_file = tmp_path / "idx.lock"

    stdout = "\n".join([
        f"MODULE:{p1.resolve()}",
        "DECL:InfoGeometry.ModA.t1:kind=theorem:partial=false:unsafe=false:axiom=false:axioms=#[propext]",
        f"MODULE:{p2.resolve()}",
        "DECL:InfoGeometry.ModB.t2:kind=theorem:partial=false:unsafe=false:axiom=false:axioms=#[Classical.choice]",
    ]) + "\n"

    with (
        patch.object(axiom_index, "ensure_compiled_axiom_index", return_value=(["/bin/ax"], None)),
        patch.object(axiom_index.subprocess, "run", return_value=SimpleNamespace(returncode=0, stdout=stdout, stderr="")) as run_mock,
    ):
        res = axiom_index.scan_olean_batch([p1, p2], olean_dir=olean_dir, lock_path=lock_file)
        assert run_mock.call_count == 1
        argv = run_mock.call_args.args[0]
        assert argv[0] == "/bin/ax"
        assert argv[1] == "--fast-modules"
        assert f"InfoGeometry.ModA={p1.resolve()}" in argv
        assert f"InfoGeometry.ModB={p2.resolve()}" in argv
        assert res[p1][1] is None and res[p1][0][0]["name"] == "InfoGeometry.ModA.t1"
        assert res[p2][1] is None and res[p2][0][0]["name"] == "InfoGeometry.ModB.t2"

        axiom_index.scan_olean_batch([p1, p2], replay=True, olean_dir=olean_dir, lock_path=lock_file)
        assert run_mock.call_args.args[0][1] == "--replay"


# --- 4. Scoped proof_proxy_staged_gate + cached T17 DAG ---------------------


def test_scoped_active_index_cache_ignores_unrelated_stages_and_catches_scoped_change(
    tmp_path: Path, monkeypatch
) -> None:
    _init_repo(tmp_path, monkeypatch)
    owner = tmp_path / "Owner.lean"
    unrelated = tmp_path / "Unrelated.lean"
    owner.write_text(gate.REQUIRED_LEAN_COPYRIGHT_HEADER + "theorem ok : True := trivial\n")
    _git(tmp_path, "add", "Owner.lean")

    cache = gate.ActiveIndexCache(tmp_path, scope_paths=["Owner.lean"])
    assert cache.still_current()

    # Concurrent staging of an unrelated file does NOT invalidate a scoped scan.
    unrelated.write_text("-- other agent work\n")
    _git(tmp_path, "add", "Unrelated.lean")
    assert cache.still_current()

    # Mutating a file inside the scoped set DOES fail closed.
    owner.write_text(gate.REQUIRED_LEAN_COPYRIGHT_HEADER + "theorem ok2 : True := trivial\n")
    _git(tmp_path, "add", "Owner.lean")
    assert not cache.still_current()


def test_proof_proxy_gate_in_memory_screening_and_strict_mode(
    tmp_path: Path, monkeypatch, capsys
) -> None:
    _init_repo(tmp_path, monkeypatch)
    shared = tmp_path / "lean" / "Pkg" / "Shared.lean"
    shared.parent.mkdir(parents=True)
    shared.write_text(
        gate.REQUIRED_LEAN_COPYRIGHT_HEADER + "theorem shared_ok : True := trivial\n",
        encoding="utf-8",
    )
    a = tmp_path / "lean" / "Pkg" / "A.lean"
    b = tmp_path / "lean" / "Pkg" / "B.lean"
    a.write_text(
        gate.REQUIRED_LEAN_COPYRIGHT_HEADER + "import Pkg.Shared\ntheorem a_ok : True := trivial\n",
        encoding="utf-8",
    )
    b.write_text(
        gate.REQUIRED_LEAN_COPYRIGHT_HEADER + "import Pkg.Shared\ntheorem b_ok : True := trivial\n",
        encoding="utf-8",
    )
    _git(tmp_path, "add", "lean/Pkg/Shared.lean", "lean/Pkg/A.lean", "lean/Pkg/B.lean")

    with patch.object(tempfile, "TemporaryDirectory", side_effect=AssertionError("unexpected tempdir")):
        rc = gate.main(["lean/Pkg/A.lean", "lean/Pkg/B.lean"])
    assert rc == 0

    # Strict mode promotes T17 warning on unwitnessed structure to failure.
    warn_file = tmp_path / "lean" / "Pkg" / "WarnOnly.lean"
    warn_file.write_text(
        gate.REQUIRED_LEAN_COPYRIGHT_HEADER + "structure UnwitnessedBox where\n  x : Nat\n",
        encoding="utf-8",
    )
    _git(tmp_path, "add", "lean/Pkg/WarnOnly.lean")
    assert gate.main(["lean/Pkg/WarnOnly.lean"]) == 0
    capsys.readouterr()
    assert gate.main(["--strict", "lean/Pkg/WarnOnly.lean"]) == 1
    assert "OpenGauss T17" in capsys.readouterr().err


def test_t17_cached_dag_propagates_multihop_taint_across_memo_reuse(tmp_path: Path) -> None:
    mod_c = tmp_path / "lean" / "Pkg" / "C.lean"
    mod_b = tmp_path / "lean" / "Pkg" / "B.lean"
    mod_c.parent.mkdir(parents=True)
    mod_c.write_text("axiom secretHole {α : Type} : α\n", encoding="utf-8")
    mod_b.write_text("import Pkg.C\ndef relayHelper {α : Type} : α := secretHole\n", encoding="utf-8")

    target = """
    import Pkg.B
    structure TargetCarrier where
      val : Nat
    def apparent : TargetCarrier := relayHelper
    """
    memo: dict = {}
    v1 = opengauss_screener.screen_lean_content(
        target, filename="A.lean", import_root=tmp_path, taint_memo=memo
    )
    assert any(v.trap_id == "T17" for v in v1)
    assert any("Pkg/B.lean" in key for key in memo)

    v2 = opengauss_screener.screen_lean_content(
        target, filename="A.lean", import_root=tmp_path, taint_memo=memo
    )
    assert any(v.trap_id == "T17" for v in v2)


# --- 5. axiom_audit scoped report guard & build_changed_lean worktree guard -


def test_axiom_audit_scoped_scan_does_not_clobber_default_report(tmp_path: Path, monkeypatch) -> None:
    report = tmp_path / "artifacts" / "axiom_audit_report.json"
    owner = tmp_path / "Owner.lean"
    owner.write_text("theorem ok : True := trivial\n", encoding="utf-8")

    with patch.object(axiom_audit, "OUTPUT_REPORT", report):
        monkeypatch.setattr("sys.argv", ["axiom_audit.py", "--fail-on-gaps", str(owner)])
        assert axiom_audit.main() == 0
        assert not report.exists()

        custom = tmp_path / "custom.json"
        monkeypatch.setattr(
            "sys.argv", ["axiom_audit.py", "--fail-on-gaps", "--output", str(custom), str(owner)]
        )
        assert axiom_audit.main() == 0
        assert custom.is_file()
        assert not report.exists()


def test_build_changed_lean_refuses_unscoped_large_dirty_worktree(tmp_path: Path, monkeypatch) -> None:
    dirty = {(tmp_path / "lean" / "InfoGeometry" / f"Mod{i}.lean").resolve() for i in range(6)}
    for p in dirty:
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text("def val : Nat := 1\n", encoding="utf-8")

    monkeypatch.setattr(build_changed_lean, "repo_root", lambda: tmp_path)
    monkeypatch.setattr(build_changed_lean, "changed_paths", lambda root, **kw: dirty)

    with patch.object(build_changed_lean, "run_locked_lake_build", return_value=0) as build_mock:
        monkeypatch.setattr("sys.argv", ["build_changed_lean.py", "--max-unscoped-modules", "3"])
        assert build_changed_lean.main() == 2
        build_mock.assert_not_called()

        monkeypatch.setattr(
            "sys.argv",
            ["build_changed_lean.py", "--max-unscoped-modules", "3", str(next(iter(dirty)))],
        )
        assert build_changed_lean.main() == 0
        assert build_mock.call_count == 1

        monkeypatch.setattr(
            "sys.argv",
            ["build_changed_lean.py", "--max-unscoped-modules", "3", "--all-changed"],
        )
        assert build_changed_lean.main() == 0
        assert build_mock.call_count == 2
