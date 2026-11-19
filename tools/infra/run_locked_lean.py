#!/usr/bin/env python3
"""Run one Lean elaboration under the repository build lock.

File-level elaboration is a compilation operation and must not race a Lake
build.  This helper keeps audit scripts on the same serialized lane as the
incremental owner builds.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
import subprocess
import sys
import tempfile
from pathlib import Path
from typing import Sequence

if __package__ in (None, ""):
    sys.path.insert(0, str(Path(__file__).resolve().parents[2]))

from tools.build_lock import BuildLockBusyError, acquire_build_lock
from tools.infra.build import _validate_lake_workspace_integrity
from tools.pathing import repo_root

_ARTIFACT_OUTPUT_FLAGS = {"-o", "-i", "-c", "-b"}
_ARTIFACT_OUTPUT_PREFIXES = ("--o=", "--i=", "--c=", "--bc=", "-o=", "-i=", "-c=", "-b=")
_ENV_CACHE_KEYS = ("LEAN_PATH", "LEAN_SRC_PATH", "LD_LIBRARY_PATH", "PATH")


def _config_fingerprint(root: Path, *, lakefile: str | None = None) -> str | None:
    """Hash Lake/toolchain files so cached LEAN_PATH invalidates automatically."""
    toolchain = root / "lean-toolchain"
    selected_lakefile = root / (lakefile or "lakefile.lean")
    if not toolchain.is_file() or not selected_lakefile.is_file():
        return None
    names = [
        "lean-toolchain",
        "lake-manifest.json",
        "lakefile.lean",
        "lakefile.toml",
    ]
    if lakefile == "lakefile.src.lean":
        names.append("lakefile.src.lean")
    digest = hashlib.sha256()
    for name in names:
        path = root / name
        digest.update(name.encode("utf-8") + b"\0")
        if path.is_file():
            try:
                digest.update(path.read_bytes())
            except OSError:
                return None
    return digest.hexdigest()


def resolve_cached_lean_env(
    root: Path, *, lake: str = "lake", lakefile: str | None = None
) -> dict[str, str] | None:
    """Resolve and cache `lake env` Lean binary + search paths per Lake lane."""
    if lake != "lake":
        return None
    fingerprint = _config_fingerprint(root, lakefile=lakefile)
    if fingerprint is None:
        return None
    cache_name = (
        "cached_lean_env_src.json" if lakefile == "lakefile.src.lean" else "cached_lean_env.json"
    )
    cache_path = root / ".lake" / cache_name
    if cache_path.is_file():
        try:
            data = json.loads(cache_path.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError):
            data = None
        if (
            isinstance(data, dict)
            and data.get("fingerprint") == fingerprint
            and isinstance(data.get("lean"), str)
            and data["lean"]
            and Path(data["lean"]).is_file()
        ):
            return {k: str(v) for k, v in data.items() if isinstance(v, str)}

    probe_code = (
        "import json, os, shutil; print(json.dumps({"
        "'lean': shutil.which('lean') or '', "
        "'leanc': shutil.which('leanc') or '', "
        "'LEAN_PATH': os.environ.get('LEAN_PATH', ''), "
        "'LEAN_SRC_PATH': os.environ.get('LEAN_SRC_PATH', ''), "
        "'LD_LIBRARY_PATH': os.environ.get('LD_LIBRARY_PATH', ''), "
        "'PATH': os.environ.get('PATH', '')"
        "}))"
    )
    cmd = [lake]
    if lakefile is not None:
        cmd.extend(("--file", lakefile))
    cmd.extend(("env", sys.executable, "-c", probe_code))
    proc = subprocess.run(cmd, cwd=root, capture_output=True, text=True, check=False)
    if proc.returncode != 0:
        return None
    lines = [ln for ln in proc.stdout.splitlines() if ln.strip()]
    if not lines:
        return None
    try:
        payload = json.loads(lines[-1])
    except json.JSONDecodeError:
        return None
    if not isinstance(payload, dict) or not payload.get("lean") or not Path(payload["lean"]).is_file():
        return None
    clean_payload = {k: str(v) for k, v in payload.items() if isinstance(v, str)}
    clean_payload["fingerprint"] = fingerprint
    try:
        cache_path.parent.mkdir(parents=True, exist_ok=True)
        fd, tmp_name = tempfile.mkstemp(
            prefix=".cached_lean_env_", suffix=".json", dir=str(cache_path.parent)
        )
        try:
            with os.fdopen(fd, "w", encoding="utf-8") as stream:
                json.dump(clean_payload, stream, indent=2, sort_keys=True)
                stream.write("\n")
            os.replace(tmp_name, cache_path)
        except BaseException:
            try:
                os.unlink(tmp_name)
            except OSError:
                pass
            raise
    except OSError:
        pass
    return clean_payload


def _writes_artifacts(lean_args: Sequence[str], *, run_script: bool) -> bool:
    """Return True if Lean flags request writing .olean/.ilean/.c/.bc outputs."""
    if run_script:
        return False
    for arg in lean_args:
        if arg in _ARTIFACT_OUTPUT_FLAGS or arg.startswith(_ARTIFACT_OUTPUT_PREFIXES):
            return True
    return False


def _merged_lean_env(
    cached: dict[str, str], base_env: dict[str, str] | None = None
) -> dict[str, str]:
    merged = dict(os.environ if base_env is None else base_env)
    for key in _ENV_CACHE_KEYS:
        value = cached.get(key)
        if value:
            merged[key] = value
    return merged


def _build_invocation(
    *,
    lake: str,
    root: Path,
    source_path: Path,
    lean_args: list[str],
    run_script: bool,
    lakefile: str | None,
    use_env_cache: bool,
    caller_env: dict[str, str] | None,
) -> tuple[list[str], dict[str, str] | None]:
    if use_env_cache:
        cached = resolve_cached_lean_env(root, lake=lake, lakefile=lakefile)
        if cached is not None:
            command = [cached["lean"]]
            if run_script:
                command.append("--run")
            command.extend([str(source_path), *lean_args])
            return command, _merged_lean_env(cached, caller_env)
    command = build_lean_command(
        lake, source_path, lean_args, run_script=run_script, lakefile=lakefile
    )
    return command, caller_env


def _resolve_repo_source(
    source: str | Path, root: Path, *, lakefile: str | None = None
) -> tuple[Path, str | None]:
    source_path = Path(source)
    if source_path.is_absolute():
        try:
            source_path = source_path.resolve().relative_to(root)
        except ValueError as exc:
            raise ValueError("Lean file must be inside the repository") from exc
    resolved_lakefile = lakefile_for_source(
        source_path, root, source_lane=lakefile == "lakefile.src.lean"
    )
    if source_path.suffix != ".lean" or not (root / source_path).is_file():
        raise ValueError(f"Lean file not found: {source_path}")
    if resolved_lakefile not in (None, "lakefile.src.lean"):
        raise ValueError("unsupported Lake configuration file")
    return source_path, resolved_lakefile


def build_lean_command(
    lake: str,
    source: Path,
    lean_args: list[str],
    *,
    run_script: bool = False,
    lakefile: str | None = None,
) -> list[str]:
    """Build the exact serialized Lake/Lean command, including source lane."""
    command = [lake]
    if lakefile is not None:
        command.extend(("--file", lakefile))
    command.extend(("env", "lean"))
    if run_script:
        command.append("--run")
    return [*command, str(source), *lean_args]


def lakefile_for_source(source: str | Path, root: Path, *, source_lane: bool = False) -> str | None:
    """Select the isolated Lake workspace for `src/` owners automatically."""
    if source_lane:
        return "lakefile.src.lean"
    path = Path(source)
    if path.is_absolute():
        try:
            path = path.resolve().relative_to(root.resolve())
        except ValueError:
            return None
    return "lakefile.src.lean" if path.parts and path.parts[0] == "src" else None


def execute_locked_lean(
    source: str | Path,
    lean_args: list[str] | None = None,
    *,
    lake: str = "lake",
    root: Path | None = None,
    wait: bool = True,
    run_script: bool = False,
    lakefile: str | None = None,
    use_env_cache: bool = True,
    shared_lock: bool | None = None,
    verbose: bool = False,
    **run_kwargs,
) -> subprocess.CompletedProcess:
    """Run Lean under the shared build lock; timeout kills the direct Lake child."""
    root = (root or repo_root()).resolve()
    integrity_error = _validate_lake_workspace_integrity(root)
    if integrity_error is not None:
        raise RuntimeError(integrity_error)
    source_path, resolved_lakefile = _resolve_repo_source(source, root, lakefile=lakefile)
    args_list = list(lean_args or [])
    is_shared = (
        not _writes_artifacts(args_list, run_script=run_script)
        if shared_lock is None
        else shared_lock
    )

    owner = f"locked-lean:{os.getpid()}:{source_path}"
    lock = acquire_build_lock(None, owner, block=wait, shared=is_shared)
    try:
        caller_env = run_kwargs.pop("env", None)
        command, merged_env = _build_invocation(
            lake=lake,
            root=root,
            source_path=source_path,
            lean_args=args_list,
            run_script=run_script,
            lakefile=resolved_lakefile,
            use_env_cache=use_env_cache,
            caller_env=caller_env,
        )
        if verbose:
            print(f"[locked-lean] executing: {' '.join(command)}", flush=True)
        if merged_env is not None:
            run_kwargs["env"] = merged_env
        return subprocess.run(command, cwd=root, check=False, **run_kwargs)
    finally:
        lock.release()


def execute_locked_lean_batch(
    sources: Sequence[str | Path],
    lean_args: list[str] | None = None,
    *,
    lake: str = "lake",
    root: Path | None = None,
    wait: bool = True,
    lakefile: str | None = None,
    use_env_cache: bool = True,
    shared_lock: bool | None = None,
    verbose: bool = True,
    **run_kwargs,
) -> int:
    """Typecheck multiple Lean files sequentially under a single build lock."""
    if not sources:
        raise ValueError("at least one Lean file is required")
    root = (root or repo_root()).resolve()
    integrity_error = _validate_lake_workspace_integrity(root)
    if integrity_error is not None:
        raise RuntimeError(integrity_error)
    resolved = [_resolve_repo_source(s, root, lakefile=lakefile) for s in sources]
    args_list = list(lean_args or [])
    is_shared = (
        not _writes_artifacts(args_list, run_script=False)
        if shared_lock is None
        else shared_lock
    )
    owner = f"locked-lean-batch:{os.getpid()}:{len(resolved)}"
    lock = acquire_build_lock(None, owner, block=wait, shared=is_shared)
    try:
        caller_env = run_kwargs.pop("env", None)
        for source_path, resolved_lakefile in resolved:
            command, merged_env = _build_invocation(
                lake=lake,
                root=root,
                source_path=source_path,
                lean_args=args_list,
                run_script=False,
                lakefile=resolved_lakefile,
                use_env_cache=use_env_cache,
                caller_env=caller_env,
            )
            if verbose:
                print(f"[locked-lean] executing: {' '.join(command)}", flush=True)
            call_kwargs = dict(run_kwargs)
            if merged_env is not None:
                call_kwargs["env"] = merged_env
            rc = subprocess.run(command, cwd=root, check=False, **call_kwargs).returncode
            if rc != 0:
                return rc
        return 0
    finally:
        lock.release()


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Run Lean under the shared build lock.")
    parser.add_argument("--wait-for-build-lock", action="store_true")
    parser.add_argument("--no-wait-for-build-lock", dest="wait", action="store_false")
    parser.set_defaults(wait=True)
    parser.add_argument("--run", action="store_true", help="Execute the source file as a Lean script.")
    parser.add_argument(
        "--source-lane",
        action="store_true",
        help="Use lakefile.src.lean and the isolated src/ artifact lane.",
    )
    parser.add_argument(
        "--no-env-cache",
        dest="use_env_cache",
        action="store_false",
        default=True,
        help="Invoke `lake env lean` instead of reusing cached LEAN_PATH.",
    )
    parser.add_argument(
        "--exclusive-lock",
        dest="shared_lock",
        action="store_false",
        default=None,
        help="Force LOCK_EX even for read-only Lean invocations.",
    )
    parser.add_argument(
        "--check-files",
        action="store_true",
        help="Check multiple Lean files under one shared lock acquisition (pass Lean flags after `--`).",
    )
    parser.add_argument("--lake", default="lake", help="Lake executable path.")
    parser.add_argument("file", nargs="?", help="Lean source file to elaborate")
    parser.add_argument("lean_args", nargs=argparse.REMAINDER)
    args = parser.parse_args(argv)

    try:
        if args.file is None:
            parser.error("the following arguments are required: file")
        lakefile_opt = "lakefile.src.lean" if args.source_lane else None
        if args.check_files:
            if args.run:
                print("--check-files cannot be combined with --run", file=sys.stderr)
                return 2
            raw_tokens = [args.file, *args.lean_args]
            if "--" in raw_tokens:
                sep = raw_tokens.index("--")
                file_tokens, extra_args = raw_tokens[:sep], raw_tokens[sep + 1 :]
            else:
                file_tokens, extra_args = raw_tokens, []
            return execute_locked_lean_batch(
                file_tokens,
                extra_args,
                lake=args.lake,
                wait=args.wait,
                lakefile=lakefile_opt,
                use_env_cache=args.use_env_cache,
                shared_lock=args.shared_lock,
                verbose=True,
            )
        return execute_locked_lean(
            args.file,
            args.lean_args,
            lake=args.lake,
            wait=args.wait,
            run_script=args.run,
            lakefile=lakefile_opt,
            use_env_cache=args.use_env_cache,
            shared_lock=args.shared_lock,
            verbose=True,
        ).returncode
    except BuildLockBusyError as exc:
        print(f"[locked-lean] build lock is held at {exc.lock_path}", file=sys.stderr)
        return 2
    except OSError as exc:
        print(f"[locked-lean] could not acquire build lock: {exc}", file=sys.stderr)
        return 126
    except (RuntimeError, ValueError) as exc:
        print(f"[locked-lean] {exc}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
