#!/usr/bin/env python3
from __future__ import annotations

import hashlib
import json
from functools import lru_cache
import os
import signal
import shlex
import subprocess
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Sequence

from tools.build_lock import BuildLock, BuildLockBusyError, acquire_build_lock
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
    packages = _declared_lake_packages(root, manifest_bytes)
    oleans = _olean_inventory(build_lib, packages)
    if not oleans:
        return ""
    compiler_identity = _lean_compiler_identity(root)
    build_identity_files = _build_identity_inventory(root)
    build_identity_state = _inventory_state(build_identity_files)
    h = hashlib.sha256()
    h.update(b"info-geometry-olean-content-v5\0")
    h.update(b"lean-compiler-identity\0" + compiler_identity.encode("utf-8") + b"\0")
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
    if _lean_compiler_identity(root) != compiler_identity:
        raise RuntimeError("Lean compiler identity changed while hashing artifacts")
    final_packages = _declared_lake_packages(root, manifest_bytes)
    if final_packages != packages:
        raise RuntimeError("Lake package inventory changed while hashing artifacts")
    final_oleans = _olean_inventory(build_lib, final_packages)
    if tuple(str(path) for path in final_oleans) != inventory:
        raise RuntimeError("olean inventory changed while hashing artifacts")
    if _inventory_state(final_oleans) != inventory_state:
        raise RuntimeError("olean files changed while hashing artifacts")
    return h.hexdigest()


def _lean_compiler_identity(root: Path) -> str:
    """Return Lean's runtime version, including its compiler commit identifier."""
    result = subprocess.run(
        ["lean", "--version"],
        cwd=root,
        check=True,
        capture_output=True,
        text=True,
    )
    identity = result.stdout.strip()
    if not identity:
        raise RuntimeError("Lean compiler returned an empty version identity")
    return identity


def compute_lean_source_hash(root: Path) -> str:
    """Content-address root and local path-package sources/configuration."""
    manifest_path = root / "lake-manifest.json"
    manifest_bytes = manifest_path.read_bytes() if manifest_path.is_file() else b""
    packages = _declared_lake_packages(root, manifest_bytes, package_types={"path"})
    files = _source_inventory(root, packages)
    if not any(path.suffix == ".lean" for path in files):
        return ""
    h = hashlib.sha256()
    h.update(b"info-geometry-source-content-v3\0")
    inventory = tuple(str(path) for path in files)
    inventory_state = _inventory_state(files)
    for path in files:
        h.update(_path_identity(path, root).encode() + b"\0")
        _hash_stable_file(h, path)
    if manifest_path.is_file() and manifest_path.read_bytes() != manifest_bytes:
        raise RuntimeError("lake manifest changed while hashing sources")
    final_packages = _declared_lake_packages(root, manifest_bytes, package_types={"path"})
    if final_packages != packages:
        raise RuntimeError("Lake package inventory changed while hashing sources")
    final_files = _source_inventory(root, final_packages)
    if tuple(str(path) for path in final_files) != inventory:
        raise RuntimeError("source inventory changed while hashing sources")
    if _inventory_state(final_files) != inventory_state:
        raise RuntimeError("source files changed while hashing sources")
    return h.hexdigest()


def _hash_stable_file(hasher: "hashlib._Hash", path: Path) -> None:
    stat_result = path.stat()
    identity = _stat_identity(stat_result)
    digest = _stable_file_digest(str(path.resolve()), identity)
    hasher.update(stat_result.st_size.to_bytes(8, "big"))
    hasher.update(digest)


@lru_cache(maxsize=100_000)
def _stable_file_digest(path: str, identity: tuple[int, int, int, int, int]) -> bytes:
    """Reuse exact content digests within one process when file identity is stable."""
    target = Path(path)
    digest = hashlib.sha256()
    try:
        with target.open("rb") as stream:
            before = os.fstat(stream.fileno())
            if _stat_identity(before) != identity:
                raise RuntimeError(f"file changed before hashing: {target}")
            while chunk := stream.read(1024 * 1024):
                digest.update(chunk)
            after = os.fstat(stream.fileno())
    except FileNotFoundError as exc:
        raise RuntimeError(f"file disappeared while hashing: {target}") from exc
    if _stat_identity(before) != _stat_identity(after):
        raise RuntimeError(f"file changed while hashing: {target}")
    try:
        current_path = target.stat()
    except FileNotFoundError as exc:
        raise RuntimeError(f"file replaced while hashing: {target}") from exc
    if _stat_identity(before) != _stat_identity(current_path):
        raise RuntimeError(f"file replaced while hashing: {target}")
    return digest.digest()


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


@dataclass(frozen=True)
class _LakePackage:
    name: str
    package_type: str
    root: Path
    revision: str | None
    sub_dir: str | None


def _declared_lake_package_records(
    root: Path, manifest: bytes, *, package_types: set[str] | None = None
) -> tuple[_LakePackage, ...]:
    """Resolve Lake package identity and effective source root from its manifest."""
    if not manifest:
        return ()
    try:
        manifest_data = json.loads(manifest)
        entries = manifest_data.get("packages", [])
    except (UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise RuntimeError("lake manifest is not valid JSON") from exc
    packages_dir_raw = manifest_data.get("packagesDir", ".lake/packages")
    if not isinstance(packages_dir_raw, str) or Path(packages_dir_raw).is_absolute():
        raise RuntimeError(f"Lake manifest has an invalid packagesDir: {packages_dir_raw!r}")
    packages_dir = (root / packages_dir_raw).resolve()
    packages: dict[tuple[str, str, Path], _LakePackage] = {}
    for item in entries:
        package_type = item.get("type")
        if package_types is not None and package_type not in package_types:
            continue
        if package_type == "path":
            name = item.get("name", "")
            if not name:
                raise RuntimeError("Lake path package has no name")
            relative = item.get("dir")
            if not isinstance(relative, str) or not relative:
                raise RuntimeError(f"Lake path package has no directory: {name}")
            package = (root / relative).resolve()
        elif package_type == "git":
            manifest_name = item.get("name", "")
            directory_name = manifest_name.strip("«»")
            if not directory_name or Path(directory_name).name != directory_name:
                raise RuntimeError(f"Lake Git package has an invalid name: {item.get('name')!r}")
            relative = item.get("dir") or str(Path(packages_dir_raw) / directory_name)
            package = (root / relative).resolve()
        else:
            raise RuntimeError(f"unsupported Lake package type: {package_type!r}")
        package_base = package
        sub_dir = item.get("subDir")
        if sub_dir is not None:
            if not isinstance(sub_dir, str) or Path(sub_dir).is_absolute():
                raise RuntimeError(f"Lake package has an invalid subDir: {sub_dir!r}")
            package = (package_base / sub_dir).resolve()
            try:
                package.relative_to(package_base)
            except ValueError as exc:
                raise RuntimeError(f"Lake package subDir escapes its package: {sub_dir!r}") from exc
        if not package.is_dir():
            raise RuntimeError(f"declared Lake package directory is unavailable: {package}")
        record = _LakePackage(
            name=name if package_type == "path" else manifest_name,
            package_type=package_type,
            root=package,
            revision=item.get("rev") if isinstance(item.get("rev"), str) else None,
            sub_dir=sub_dir,
        )
        packages[(record.name, record.package_type, record.root)] = record
    return tuple(packages[key] for key in sorted(packages))


def _declared_lake_packages(
    root: Path, manifest: bytes, *, package_types: set[str] | None = None
) -> tuple[Path, ...]:
    """Resolve Lake package roots, optionally restricted by manifest type."""
    return tuple(
        record.root for record in
        _declared_lake_package_records(root, manifest, package_types=package_types)
    )


def _olean_inventory(build_lib: Path, dependencies: Sequence[Path]) -> list[Path]:
    """Inventory main and optional OLean parts that Lean imports together."""
    paths: set[Path] = set()
    patterns = ("*.olean", "*.olean.server", "*.olean.private")
    if build_lib.is_dir():
        for pattern in patterns:
            paths.update(build_lib.rglob(pattern))
    for package in dependencies:
        package_lib = package / ".lake" / "build" / "lib"
        if package_lib.is_dir():
            for pattern in patterns:
                paths.update(package_lib.rglob(pattern))
    return sorted(path.resolve() for path in paths if path.is_file())


def _source_inventory(root: Path, dependencies: Sequence[Path]) -> list[Path]:
    """List project/package Lean sources while excluding VCS and build internals."""
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
    # Keep root and Lake package inputs relocatable across checkout roots.
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
    targets: Sequence[str], *, wait_for_lock: bool = False, wfail: bool = False,
    existing_lock: BuildLock | None = None,
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
        # A compound operation such as declaration refresh may already hold
        # the shared lock across hashing, building, and indexing. Re-enter the
        # same BuildLock object so this build cannot release the caller's lock.
        lock = (acquire_build_lock(None, owner, block=wait_for_lock)
                if existing_lock is None else existing_lock.acquire())
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
    status = 126
    proc: subprocess.Popen[bytes] | None = None
    interrupted = False
    try:
        _ensure_mathlib_cache_hydrated(root)
        cmd = lake_build_command(targets, wfail=wfail)
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
    build_lock: BuildLock | None = None,
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
        if build_lock is None:
            subprocess.run(cmd, cwd=root, check=True)
        else:
            status = run_locked_lake_build(
                [prebuild_target, build_target],
                wait_for_lock=False,
                existing_lock=build_lock,
            )
            if status != 0:
                raise subprocess.CalledProcessError(status, cmd)
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
