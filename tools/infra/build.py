#!/usr/bin/env python3
from __future__ import annotations

import hashlib
import os
import subprocess
import sys
from pathlib import Path
from typing import Sequence

from tools.build_lock import BuildLockBusyError, acquire_build_lock
from tools.pathing import repo_root

_SPECTRAL_STAGE_PREFIX: dict[str, str] = {
    "PREP": "[Sample Preparation]",
    "DECOMP": "[Spectral Decomposition]",
    "CONGEST": "[Band Congestion Analysis]",
    "ASSIGN": "[Line Assignment]",
    "PAULI": "[Selection-Rule Enforcement]",
    "CRYSTAL": "[Crystallized Assignment]",
    "ATLAS": "[Spectral Atlas]",
}


def log_spectral_stage(stage: str, module: str, details: str = "") -> None:
    """Emit build-lane status using spectroscopic workflow terminology."""
    prefix = _SPECTRAL_STAGE_PREFIX.get(stage, "[UNKNOWN]")
    tail = f" {details}" if details else ""
    print(f"{prefix} {module}{tail}", flush=True)


def compute_olean_content_hash(root: Path) -> str:
    """Compute a fast content hash over .olean files to detect environment changes."""
    build_lib = root / ".lake" / "build" / "lib"
    if not build_lib.exists():
        build_lib = root / ".build" / "lib"
    if not build_lib.exists():
        return ""
    oleans = sorted(build_lib.rglob("*.olean"))
    h = hashlib.sha256()
    for path in oleans:
        stat = path.stat()
        h.update(str(path.relative_to(build_lib)).encode())
        h.update(str(stat.st_mtime_ns).encode())
        h.update(str(stat.st_size).encode())
    return h.hexdigest()


def compute_lean_source_hash(root: Path) -> str:
    """Compute a content hash over Lean source/config inputs relevant to decl indexing."""
    lean_root = root / "lean"
    if not lean_root.exists():
        return ""
    lean_files = sorted(lean_root.rglob("*.lean"))
    if not lean_files:
        return ""
    h = hashlib.sha256()
    for path in lean_files:
        try:
            stat = path.stat()
        except FileNotFoundError:
            # Concurrent source edits should not crash hash computation.
            continue
        h.update(str(path.relative_to(root)).encode())
        h.update(str(stat.st_mtime_ns).encode())
        h.update(str(stat.st_size).encode())

    for extra in ("lakefile.lean", "lakefile.toml", "lean-toolchain"):
        extra_path = root / extra
        if not extra_path.exists():
            continue
        stat = extra_path.stat()
        h.update(extra.encode())
        h.update(str(stat.st_mtime_ns).encode())
        h.update(str(stat.st_size).encode())
    return h.hexdigest()


def run_locked_lake_build(
    targets: Sequence[str], *, wait_for_lock: bool = False, wfail: bool = False
) -> int:
    root = repo_root()
    target_label = " ".join(targets) if targets else "<default>"
    owner = f"locked-lake-build:{os.getpid()}:{target_label}"
    log_spectral_stage("PREP", target_label, "establishing locked build vacuum")
    try:
        lock = acquire_build_lock(None, owner, block=wait_for_lock)
    except BuildLockBusyError as exc:
        meta = exc.metadata or {}
        owner_msg = meta.get("owner", "unknown")
        pid_msg = meta.get("pid", "unknown")
        print(
            f"[locked-lake-build] another build already holds {exc.lock_path} "
            f"(owner={owner_msg}, pid={pid_msg}); refusing to start a concurrent build",
            file=sys.stderr,
            flush=True,
        )
        return 2

    cmd = ["lake", "build"]
    if wfail:
        cmd.append("--wfail")
        log_spectral_stage("PAULI", target_label, "warnings promoted to errors (--wfail)")
    else:
        log_spectral_stage("ASSIGN", target_label, "running default selection rules")
    cmd.extend(targets)
    print(f"[locked-lake-build] acquired {lock.lock_path}", flush=True)
    log_spectral_stage("DECOMP", target_label, f"lock acquired at {lock.lock_path}")
    print(f"[locked-lake-build] running: {' '.join(cmd)}", flush=True)
    try:
        proc = subprocess.run(cmd, cwd=root)
        if proc.returncode == 0:
            log_spectral_stage("CRYSTAL", target_label, "stable closure achieved")
        else:
            log_spectral_stage(
                "CONGEST",
                target_label,
                f"build exited with code {proc.returncode}",
            )
        return proc.returncode
    finally:
        lock.release()
        print(f"[locked-lake-build] released {lock.lock_path}", flush=True)
        log_spectral_stage("ATLAS", target_label, "lock released; registry ready for refresh")


def ensure_built_executable(root: Path, target: str) -> Path:
    """Ensure a Lake executable target exists under `.lake/build/bin`."""
    built = root / ".lake" / "build" / "bin" / target
    if built.exists():
        return built
    rc = run_locked_lake_build([target], wait_for_lock=True)
    if rc != 0:
        raise RuntimeError(f"failed to build required executable target: {target}")
    if not built.exists():
        raise RuntimeError(
            f"expected built executable {built} after successful build of {target}"
        )
    return built


def build_indexer_command(
    root: Path,
    import_root: str,
    namespace: str,
    index_dir: Path,
    graph_out: Path,
    structure_out: Path,
    *,
    run_mode: str,
) -> list[str]:
    if run_mode == "exe":
        built_exe = root / ".lake" / "build" / "bin" / "dagIndexer"
        if built_exe.exists():
            return [
                "lake",
                "env",
                str(built_exe),
                import_root,
                namespace,
                str(index_dir),
                str(graph_out),
                str(structure_out),
            ]
        return [
            "lake",
            "exe",
            "dagIndexer",
            import_root,
            namespace,
            str(index_dir),
            str(graph_out),
            str(structure_out),
        ]
    return [
        "lake",
        "env",
        "lean",
        "--run",
        "lean/DAG/Indexer.lean",
        import_root,
        namespace,
        str(index_dir),
        str(graph_out),
        str(structure_out),
    ]


def run_locked_prebuild(
    root: Path,
    build_target: str,
    *,
    run_mode: str = "exe",
    python_executable: str | None = None,
    allow_failure: bool = False,
) -> bool:
    prebuild_target = "dagIndexer" if run_mode == "exe" else "DAG.Indexer"
    cmd = [
        python_executable or sys.executable,
        "tools/infra/run_locked_lake_build.py",
        "--wait-for-build-lock",
        prebuild_target,
        build_target,
    ]
    print(f"[refresh-decl-graph] prebuilding with lock: {' '.join(cmd)}", flush=True)
    try:
        subprocess.run(cmd, cwd=root, check=True)
        return True
    except subprocess.CalledProcessError as exc:
        if not allow_failure:
            raise RuntimeError(
                "[refresh-decl-graph] prebuild failed; refusing to continue with indexing "
                f"(target={build_target}, exit={exc.returncode}). "
                "Fix the build or rerun with --allow-prebuild-failure."
            ) from exc
        print(
            "[refresh-decl-graph] prebuild failed; continuing with direct indexer run "
            f"(exit={exc.returncode})",
            file=sys.stderr,
            flush=True,
        )
        return False
