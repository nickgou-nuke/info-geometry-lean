#!/usr/bin/env python3
from __future__ import annotations

import hashlib
import json
import os
import signal
import shlex
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
    """Content-address built oleans and pinned build inputs for DAG cache safety."""
    build_lib = root / ".lake" / "build" / "lib"
    if not build_lib.exists():
        build_lib = root / ".build" / "lib"
    manifest_path = root / "lake-manifest.json"
    manifest_bytes = manifest_path.read_bytes() if manifest_path.is_file() else b""
    dependencies = _declared_path_dependencies(root, manifest_bytes)
    oleans = _olean_inventory(build_lib, dependencies)
    if not oleans:
        return ""
    build_identity_files = _build_identity_inventory(root)
    build_identity_state = _inventory_state(build_identity_files)
    h = hashlib.sha256()
    h.update(b"info-geometry-olean-content-v2\0")
    for name in ("lean-toolchain", "lakefile.lean", "lakefile.toml"):
        path = root / name
        h.update(name.encode() + b"\0")
        if path.is_file():
            _hash_stable_file(h, path)
    h.update(b"lake-manifest.json\0" + manifest_bytes)
    inventory = tuple(str(path) for path in oleans)
    inventory_state = _inventory_state(oleans)
    for path in oleans:
        h.update(_path_identity(path, root).encode() + b"\0")
        _hash_stable_file(h, path)
    if manifest_path.is_file() and manifest_path.read_bytes() != manifest_bytes:
        raise RuntimeError("lake manifest changed while hashing artifacts")
    final_identity_files = _build_identity_inventory(root)
    if tuple(map(str, final_identity_files)) != tuple(map(str, build_identity_files)):
        raise RuntimeError("build configuration inventory changed while hashing artifacts")
    if _inventory_state(final_identity_files) != build_identity_state:
        raise RuntimeError("build configuration changed while hashing artifacts")
    final_oleans = _olean_inventory(build_lib, dependencies)
    if tuple(str(path) for path in final_oleans) != inventory:
        raise RuntimeError("olean inventory changed while hashing artifacts")
    if _inventory_state(final_oleans) != inventory_state:
        raise RuntimeError("olean files changed while hashing artifacts")
    return h.hexdigest()


def compute_lean_source_hash(root: Path) -> str:
    """Content-address Lean sources, path-package sources, and build configuration."""
    manifest_path = root / "lake-manifest.json"
    manifest_bytes = manifest_path.read_bytes() if manifest_path.is_file() else b""
    dependencies = _declared_path_dependencies(root, manifest_bytes)
    files = _source_inventory(root, dependencies)
    if not any(path.suffix == ".lean" for path in files):
        return ""
    h = hashlib.sha256()
    h.update(b"info-geometry-source-content-v2\0")
    inventory = tuple(str(path) for path in files)
    inventory_state = _inventory_state(files)
    for path in files:
        h.update(_path_identity(path, root).encode() + b"\0")
        _hash_stable_file(h, path)
    if manifest_path.is_file() and manifest_path.read_bytes() != manifest_bytes:
        raise RuntimeError("lake manifest changed while hashing sources")
    final_files = _source_inventory(root, dependencies)
    if tuple(str(path) for path in final_files) != inventory:
        raise RuntimeError("source inventory changed while hashing sources")
    if _inventory_state(final_files) != inventory_state:
        raise RuntimeError("source files changed while hashing sources")
    return h.hexdigest()


def _hash_stable_file(hasher: "hashlib._Hash", path: Path) -> None:
    with path.open("rb") as stream:
        before = os.fstat(stream.fileno())
        hasher.update(before.st_size.to_bytes(8, "big"))
        while chunk := stream.read(1024 * 1024):
            hasher.update(chunk)
        after = os.fstat(stream.fileno())
    if _stat_identity(before) != _stat_identity(after):
        raise RuntimeError(f"file changed while hashing: {path}")
    try:
        current_path = path.stat()
    except FileNotFoundError as exc:
        raise RuntimeError(f"file replaced while hashing: {path}") from exc
    if _stat_identity(before) != _stat_identity(current_path):
        raise RuntimeError(f"file replaced while hashing: {path}")


def _stat_identity(stat_result: os.stat_result) -> tuple[int, int, int, int, int]:
    return (
        stat_result.st_dev,
        stat_result.st_ino,
        stat_result.st_size,
        stat_result.st_mtime_ns,
        stat_result.st_ctime_ns,
    )


def _inventory_state(paths: Sequence[Path]) -> tuple[tuple[str, tuple[int, int, int, int, int]], ...]:
    try:
        return tuple((str(path), _stat_identity(path.stat())) for path in paths)
    except FileNotFoundError as exc:
        raise RuntimeError("file inventory changed while hashing") from exc


def _declared_path_dependencies(root: Path, manifest: bytes) -> tuple[Path, ...]:
    if not manifest:
        return ()
    try:
        packages = json.loads(manifest).get("packages", [])
    except (UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise RuntimeError("lake manifest is not valid JSON") from exc
    paths = set()
    for item in packages:
        if item.get("type") != "path" or not item.get("dir"):
            continue
        path = (root / item["dir"]).resolve()
        if not path.is_dir():
            raise RuntimeError(f"declared Lake path dependency is unavailable: {item['dir']}")
        paths.add(path)
    return tuple(sorted(paths))


def _olean_inventory(build_lib: Path, dependencies: Sequence[Path]) -> list[Path]:
    paths = set(build_lib.rglob("*.olean")) if build_lib.is_dir() else set()
    for package in dependencies:
        package_lib = package / ".lake" / "build" / "lib"
        if package_lib.is_dir():
            paths.update(package_lib.rglob("*.olean"))
    return sorted(path.resolve() for path in paths if path.is_file())


def _source_inventory(root: Path, dependencies: Sequence[Path]) -> list[Path]:
    paths = set((root / "lean").rglob("*.lean")) if (root / "lean").is_dir() else set()
    for package in dependencies:
        paths.update(
            path for path in package.rglob("*.lean")
            if not {".git", ".lake"}.intersection(path.relative_to(package).parts)
        )
        for name in ("lakefile.lean", "lakefile.toml", "lean-toolchain", "lake-manifest.json"):
            config = package / name
            if config.is_file():
                paths.add(config)
    for name in ("lakefile.lean", "lakefile.toml", "lean-toolchain", "lake-manifest.json"):
        path = root / name
        if path.is_file():
            paths.add(path)
    return sorted(path.resolve() for path in paths if path.is_file())


def _build_identity_inventory(root: Path) -> list[Path]:
    names = ("lean-toolchain", "lakefile.lean", "lakefile.toml", "lake-manifest.json")
    return [root / name for name in names if (root / name).is_file()]


def _path_identity(path: Path, root: Path) -> str:
    # Keep external Lake `type = path` dependencies relocatable when the same
    # project/dependency layout is checked out under a different absolute root.
    return Path(os.path.relpath(path.resolve(), root.resolve())).as_posix()


def lake_build_command(targets: Sequence[str], *, wfail: bool = False) -> list[str]:
    """Compile the exact Lake argv after wrapper-owned options are resolved."""
    command = ["lake", "build"]
    if wfail:
        command.append("--wfail")
    command.extend(targets)
    return command


def _interrupt_child_and_wait(proc: subprocess.Popen[bytes]) -> None:
    """Forward Ctrl-C to Lake and keep owning the lock until it exits."""
    if proc.poll() is not None:
        return
    try:
        if os.name == "posix":
            os.killpg(proc.pid, signal.SIGINT)
        else:
            proc.send_signal(signal.SIGINT)
    except ProcessLookupError:
        pass
    except OSError as exc:
        print(
            f"[locked-lake-build] could not forward interrupt ({exc}); "
            "retaining the lock until the Lake process exits",
            file=sys.stderr,
            flush=True,
        )

    # Repeated Ctrl-C must not release the shared lock while Lake remains alive.
    while proc.poll() is None:
        try:
            proc.wait()
        except KeyboardInterrupt:
            continue


def _validate_lake_workspace_integrity(root: Path) -> str | None:
    """Reject linked worktrees or symlinked .lake directories that cause Lake
    to treat shared packages as URL changes and wipe .lake/packages/mathlib."""
    lake_dir = root / ".lake"
    git_entry = root / ".git"
    if lake_dir.is_symlink():
        return (
            f"refusing to run Lake with symlinked .lake ({lake_dir} -> {lake_dir.resolve()}); "
            "symlinked .lake across worktrees causes Lake to delete and re-clone mathlib"
        )
    if git_entry.is_file():
        return (
            f"refusing to run Lake inside a linked git worktree ({root}); "
            "run builds only from the primary repository checkout"
        )
    packages_dir = lake_dir / "packages"
    if packages_dir.is_symlink():
        return f"refusing to run Lake with symlinked .lake/packages ({packages_dir})"
    return None


def _ensure_mathlib_cache_hydrated(root: Path) -> None:
    """If .lake/packages/mathlib was freshly cloned without .olean files, hydrate
    from the local ~/.cache/mathlib archive via `lake exe cache get` before building."""
    mathlib_dir = root / ".lake" / "packages" / "mathlib"
    if not mathlib_dir.exists():
        return
    mathlib_lib = mathlib_dir / ".lake" / "build" / "lib" / "lean" / "Mathlib"
    if mathlib_lib.exists() and any(mathlib_lib.rglob("*.olean")):
        return
    print(
        "[locked-lake-build] .lake/packages/mathlib has no compiled .olean cache; "
        "hydrating via `lake exe cache get`...",
        flush=True,
    )
    subprocess.run(["lake", "exe", "cache", "get"], cwd=root, check=False)


def run_locked_lake_build(
    targets: Sequence[str], *, wait_for_lock: bool = False, wfail: bool = False
) -> int:
    """Run the causal build transaction: validate -> lock -> execute -> release.

    Child stdout/stderr are inherited so diagnostics are visible as Lake emits them.
    """
    root = repo_root()
    integrity_error = _validate_lake_workspace_integrity(root)
    if integrity_error is not None:
        print(f"[locked-lake-build] {integrity_error}", file=sys.stderr, flush=True)
        return 2
    targets = tuple(str(target) for target in targets)
    if any(not target or "\x00" in target for target in targets):
        print("[locked-lake-build] invalid empty/NUL target argument", file=sys.stderr, flush=True)
        return 2
    target_label = " ".join(targets) if targets else "<default>"
    owner = f"locked-lake-build:{os.getpid()}:{target_label}"
    print(f"[locked-lake-build] requesting lock for {target_label}", flush=True)
    try:
        lock = acquire_build_lock(None, owner, block=wait_for_lock)
    except BuildLockBusyError as exc:
        meta = exc.metadata or {}
        owner_msg = meta.get("owner", "unknown")
        pid_msg = meta.get("pid", "unknown")
        print(
            f"[locked-lake-build] lock is held at {exc.lock_path} "
            f"(recorded owner={owner_msg}, pid={pid_msg}); refusing concurrent build",
            file=sys.stderr,
            flush=True,
        )
        return 2
    except OSError as exc:
        print(f"[locked-lake-build] could not acquire build lock: {exc}",
              file=sys.stderr, flush=True)
        return 126
    except KeyboardInterrupt:
        print("[locked-lake-build] interrupted while waiting for build lock",
              file=sys.stderr, flush=True)
        return 130

    print(f"[locked-lake-build] acquired {lock.lock_path}", flush=True)
    _ensure_mathlib_cache_hydrated(root)
    cmd = lake_build_command(targets, wfail=wfail)
    status = 126
    proc: subprocess.Popen[bytes] | None = None
    interrupted = False
    try:
        print(f"[locked-lake-build] executing: {shlex.join(cmd)}", flush=True)
        proc = subprocess.Popen(cmd, cwd=root, start_new_session=(os.name == "posix"))
        try:
            status = proc.wait()
        except KeyboardInterrupt:
            interrupted = True
            raise
        print(f"[locked-lake-build] lake build exited with code {status}", flush=True)
    except FileNotFoundError as exc:
        print(f"[locked-lake-build] could not start build command: {exc}",
              file=sys.stderr, flush=True)
        status = 127
    except OSError as exc:
        print(f"[locked-lake-build] build launch failed: {exc}",
              file=sys.stderr, flush=True)
        status = 126
    except KeyboardInterrupt:
        interrupted = True
        print("[locked-lake-build] interrupted by user", file=sys.stderr, flush=True)
        if proc is not None:
            _interrupt_child_and_wait(proc)
        status = 130
    finally:
        try:
            lock.release()
            print(f"[locked-lake-build] released {lock.lock_path}", flush=True)
        except OSError as exc:
            print(f"[locked-lake-build] failed to release lock: {exc}",
                  file=sys.stderr, flush=True)
            if status == 0 and not interrupted:
                status = 126
    return status


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
