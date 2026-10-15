#!/usr/bin/env python3
"""Compute a local reproducibility manifest for a Pantograph Lean session."""

from __future__ import annotations

import hashlib
import json
import re
import subprocess
from pathlib import Path
from typing import Any, Callable


def canonical_json(value: Any) -> str:
    return json.dumps(value, sort_keys=True, ensure_ascii=False, separators=(",", ":"))


def sha256_bytes(value: bytes) -> str:
    return hashlib.sha256(value).hexdigest()


def sha256_file(path: Path) -> str:
    return sha256_bytes(path.read_bytes())


def _run(args: list[str], root: Path, runner: Callable[..., Any], input_text: str | None = None) -> str:
    result = runner(args, cwd=root, check=False, capture_output=True, text=True, input=input_text)
    if result.returncode != 0:
        raise RuntimeError(f"command failed ({result.returncode}): {' '.join(args)}\n{result.stderr[-2000:]}")
    return result.stdout.strip()


def _relative_identity(path: Path, root: Path, lean_lib: Path) -> str:
    resolved = path.resolve()
    try:
        return "project:" + resolved.relative_to(root).as_posix()
    except ValueError:
        pass
    try:
        return "leanlib:" + resolved.relative_to(lean_lib.resolve()).as_posix()
    except ValueError:
        return "absolute:" + str(resolved)


def _pantograph_root(command: list[str], cwd: Path) -> tuple[Path, Path, int] | None:
    for index, arg in enumerate(command):
        candidate = Path(arg)
        if not candidate.is_absolute():
            candidate = cwd / candidate
        if not candidate.is_file():
            continue
        for parent in candidate.resolve().parents:
            if (parent / "Repl.lean").is_file() and (parent / ".git").exists():
                return parent, candidate.resolve(), index
    return None


def _tree_fingerprint(root: Path, runner: Callable[..., Any]) -> tuple[str, str]:
    head = _run(["git", "rev-parse", "HEAD"], root, runner)
    listing = _run(["git", "ls-files", "-co", "--exclude-standard", "-z"], root, runner)
    paths = sorted({item for item in listing.split("\0") if item})
    excluded = {".git", ".lake", "build", "dist", "node_modules", "target"}
    hasher = hashlib.sha256()
    for relative in paths:
        path = Path(relative)
        if excluded.intersection(path.parts):
            continue
        full_path = root / path
        if not full_path.is_file():
            continue
        data = full_path.read_bytes()
        hasher.update(path.as_posix().encode("utf-8"))
        hasher.update(b"\0")
        hasher.update(len(data).to_bytes(8, "big"))
        hasher.update(data)
    return head, hasher.hexdigest()


def build_lean_context_manifest(
    project_root: Path,
    source_path: Path,
    *,
    runner: Callable[..., Any] = subprocess.run,
) -> dict[str, Any]:
    """Fingerprint the exact Lean/Lake context for one source, excluding Pantograph."""
    root = project_root.resolve()
    source = source_path.resolve() if source_path.is_absolute() else (root / source_path).resolve()
    try:
        source_relative = source.relative_to(root).as_posix()
    except ValueError as exc:
        raise RuntimeError("source snapshot must be inside the project root") from exc
    if not source.is_file():
        raise RuntimeError(f"source snapshot is unavailable: {source}")
    required = {name: root / name for name in ("lean-toolchain", "lakefile.lean", "lake-manifest.json")}
    if any(not path.is_file() for path in required.values()):
        raise RuntimeError("required Lean/Lake build identity file is missing")
    deps = _run(["lake", "env", "lean", "--deps", str(source)], root, runner)
    lean_lib = Path(_run(["lake", "env", "lean", "--print-libdir"], root, runner))
    paths = {Path(line).resolve() for line in deps.splitlines() if line.strip().endswith(".olean")}
    if source_relative.startswith("lean/"):
        target = root / ".lake" / "build" / "lib" / "lean" / source_relative.removeprefix("lean/")
        paths.add(target.with_suffix(".olean").resolve())
    if not paths:
        raise RuntimeError("Lean dependency query returned no .olean inputs")
    missing = sorted(str(path) for path in paths if not path.is_file())
    if missing:
        raise RuntimeError("required source .olean files are missing: " + ", ".join(missing[:8]))
    olean_inputs = [
        {"path": _relative_identity(path, root, lean_lib), "sha256": sha256_file(path)}
        for path in sorted(paths, key=lambda item: _relative_identity(item, root, lean_lib))
    ]
    payload: dict[str, Any] = {
        "schema": "info_geometry.lean_source_context.v1",
        "toolchainSha256": sha256_file(required["lean-toolchain"]),
        "lakefileSha256": sha256_file(required["lakefile.lean"]),
        "lakeManifestSha256": sha256_file(required["lake-manifest.json"]),
        "sourcePath": source_relative,
        "sourceSha256": sha256_file(source),
        "leanVersion": _run(["lake", "env", "lean", "--version"], root, runner),
        "lakeVersion": _run(["lake", "--version"], root, runner),
        "sourceLeanOleans": olean_inputs,
    }
    payload["fingerprint"] = sha256_bytes(canonical_json(payload).encode("utf-8"))
    return payload


def build_environment_manifest(
    project_root: Path,
    source_path: Path,
    command: list[str],
    *,
    runner: Callable[..., Any] = subprocess.run,
) -> dict[str, Any]:
    """Hash source, lockfiles, loaded import oleans, and the Pantograph checkout.

    `lean --deps` is a dependency query only; it does not compile or write
    artifacts. The caller supplies the already-built REPL command.
    """
    root = project_root.resolve()
    source = source_path.resolve() if source_path.is_absolute() else (root / source_path).resolve()
    try:
        source_relative = source.relative_to(root).as_posix()
    except ValueError as exc:
        raise RuntimeError("source snapshot must be inside the project root") from exc
    if not source.is_file():
        raise RuntimeError(f"source snapshot is unavailable: {source}")
    for required in (root / "lean-toolchain", root / "lakefile.lean", root / "lake-manifest.json"):
        if not required.is_file():
            raise RuntimeError(f"required build identity file is missing: {required}")

    source_context = build_lean_context_manifest(root, source, runner=runner)
    deps_output = _run(["lake", "env", "lean", "--deps", str(source)], root, runner)
    lean_lib = Path(_run(["lake", "env", "lean", "--print-libdir"], root, runner))
    olean_paths = {Path(line).resolve() for line in deps_output.splitlines() if line.strip().endswith(".olean")}
    pantograph = _pantograph_root(command, root)
    if pantograph is None:
        raise RuntimeError("could not locate the Pantograph source checkout from the recorded command")
    pantograph_root, executable, executable_index = pantograph
    startup_modules = sorted({
        arg for arg in command[executable_index + 1:]
        if re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)*", arg)
    })
    # Ask Lean for the complete import closure of every module Pantograph loads
    # at startup, even when that module is not imported by the captured source.
    for module_name in startup_modules:
        module_deps = _run(
            ["lake", "env", "lean", "--deps", "--stdin"], root, runner,
            input_text=f"import {module_name}\n",
        )
        olean_paths.update(
            Path(line).resolve() for line in module_deps.splitlines()
            if line.strip().endswith(".olean")
        )
    # Include the target module's own compiled artifact; --deps lists imports.
    if source_relative.startswith("lean/"):
        target_olean = root / ".lake" / "build" / "lib" / "lean" / source_relative.removeprefix("lean/")
        olean_paths.add(target_olean.with_suffix(".olean").resolve())
    if not olean_paths:
        raise RuntimeError("Lean dependency query returned no .olean inputs")
    missing = sorted(str(path) for path in olean_paths if not path.is_file())
    if missing:
        raise RuntimeError("required imported .olean files are missing: " + ", ".join(missing[:8]))
    olean_inputs = [
        {"path": _relative_identity(path, root, lean_lib), "sha256": sha256_file(path)}
        for path in sorted(olean_paths, key=lambda p: _relative_identity(p, root, lean_lib))
    ]

    pantograph_head, pantograph_tree = _tree_fingerprint(pantograph_root, runner)

    payload: dict[str, Any] = {
        "schema": "info_geometry.pantograph_environment.v1",
        "projectRootName": root.name,
        "toolchainSha256": sha256_file(root / "lean-toolchain"),
        "lakefileSha256": sha256_file(root / "lakefile.lean"),
        "lakeManifestSha256": sha256_file(root / "lake-manifest.json"),
        "sourcePath": source_relative,
        "sourceSha256": sha256_file(source),
        "startupModules": startup_modules,
        "leanVersion": _run(["lake", "env", "lean", "--version"], root, runner),
        "lakeVersion": _run(["lake", "--version"], root, runner),
        "leanOleans": olean_inputs,
        "leanContextFingerprint": source_context["fingerprint"],
        "leanSourceContext": source_context,
        "pantograph": {
            "rootName": pantograph_root.name,
            "gitHead": pantograph_head,
            "sourceTreeSha256": pantograph_tree,
            "replExecutableSha256": sha256_file(executable),
        },
    }
    payload["fingerprint"] = sha256_bytes(canonical_json(payload).encode("utf-8"))
    return payload


def manifest_fingerprint(manifest: dict[str, Any]) -> str:
    payload = {key: value for key, value in manifest.items() if key != "fingerprint"}
    return sha256_bytes(canonical_json(payload).encode("utf-8"))


def verify_environment_match(recorded: dict[str, Any], current: dict[str, Any]) -> None:
    """Fail closed on a corrupt saved manifest or any live-input drift."""
    recorded_fingerprint = recorded.get("fingerprint")
    current_fingerprint = current.get("fingerprint")
    if not isinstance(recorded_fingerprint, str) or manifest_fingerprint(recorded) != recorded_fingerprint:
        raise RuntimeError("stored environment manifest fingerprint is inconsistent")
    if not isinstance(current_fingerprint, str) or manifest_fingerprint(current) != current_fingerprint:
        raise RuntimeError("current environment manifest fingerprint is inconsistent")
    if current_fingerprint != recorded_fingerprint:
        raise RuntimeError(
            "current toolchain, Lake inputs, imported oleans, Pantograph sources, or REPL binary differ"
        )
