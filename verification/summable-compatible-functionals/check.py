#!/usr/bin/env python3
"""Check exact summable-compatibility sources in an isolated, pinned Lake project.

This is a focused check, not the root package build or publication gate. Source
files and dependency pins remain unchanged. All compiler commands share one
exclusive transaction using the repository's maintained build lock.
"""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import time

DEFAULT_OWNERS = (
    "InfoGeometry.Canonical.SummableCompatibleFunctionals",
)


def locate_repo() -> Path:
    for directory in Path(__file__).resolve().parents:
        if (directory / "AGENTS.md").is_file() and (directory / "lakefile.lean").is_file():
            return directory
    return Path(__file__).resolve().parents[1] / "info-geometry-lean"


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def require(condition: bool, message: str) -> None:
    if not condition:
        raise RuntimeError(message)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo-root", type=Path, default=locate_repo())
    parser.add_argument("--work", type=Path,
                        help="Isolated build directory; existing caches are preserved")
    parser.add_argument("--package-root", type=Path,
                        help="Directory containing all nine exact pinned Git dependencies")
    parser.add_argument("--phase", choices=("build", "audit", "final"), default="final",
                        help="build: incremental compile only; audit: rebuild and inspect axioms; final: both and fresh checks")
    parser.add_argument("--no-wait", action="store_true",
                        help="Fail immediately if the maintained shared build lock is held")
    args = parser.parse_args()
    root = args.repo_root.resolve()
    work = (args.work or root.parent / "summable-compatible-build").resolve()
    package_root = (args.package_root or root / ".lake/packages").resolve()
    require(work != root and root not in work.parents,
            "Use a separate working directory outside the repository")
    require(package_root.is_dir(), f"Pinned package directory is missing: {package_root}")
    # Capture executable controls before importing them or waiting for the lock.
    # A queued run must not certify new on-disk helpers while executing old imports.
    controls = (
        root / "lean-toolchain", root / "lake-manifest.json", root / "lakefile.lean",
        root / "verification/real-matrix-split/lean-toolchain",
        root / "verification/real-matrix-split/lake-manifest.json",
        root / "tools/build_lock.py", root / "tools/infra/build.py",
        root / "tools/pathing.py",
        root / "tools/__init__.py", root / "tools/infra/__init__.py",
        root / "tools/quality/__init__.py",
        root / "tools/quality/check_reviewed_prs.py",
        root / "tools/quality/reviewed_audit_source.py",
        root / ".github/workflows/summable-compatible-functionals.yml", Path(__file__).resolve(),
    )
    control_hashes = {str(p): digest(p) for p in controls}
    sys.path.insert(0, str(root))
    from tools.build_lock import acquire_build_lock
    from tools.infra.build import _interrupt_child_and_wait, _validate_lake_workspace_integrity
    from tools.quality.check_reviewed_prs import closure
    from tools.quality.reviewed_audit_source import audit_source, parse_audit_output, validate_targets

    owners = tuple(validate_targets(DEFAULT_OWNERS))
    require(all(m.startswith("InfoGeometry.") for m in owners),
            "The focused library owns InfoGeometry modules only")
    for directory in (root, work):
        error = _validate_lake_workspace_integrity(directory)
        require(error is None, error or "Invalid workspace")
    work.mkdir(parents=True, exist_ok=True)
    marker = work / "summable-compatible-project.json"
    if marker.exists():
        previous = json.loads(marker.read_text())
        require(previous.get("source_root") == str(root),
                "Work directory belongs to another source checkout")
    elif any(work.iterdir()):
        raise RuntimeError("Select an empty work directory or an existing summable-compatibility project")
    marker.write_text(json.dumps({"source_root": str(root)}, indent=2) + "\n")
    run_id = f"run-{time.time_ns()}-{os.getpid()}"
    logs = work / "logs" / run_id
    logs.mkdir(parents=True)
    receipt = work / "status.json"
    status = {
        "status": "queued", "run_id": run_id, "phase": args.phase,
        "started_at": datetime.now(timezone.utc).isoformat(),
        "source_root": str(root), "work": str(work), "owners": owners,
        "package_root": str(package_root), "commands": [],
        "root_package_build_verified": False,
        "publication_gate_verified": False,
        "independent_semantic_review_verified_by_this_runner": False,
    }

    def save() -> None:
        temporary = work / f"status.{run_id}.tmp"
        temporary.write_text(json.dumps(status, indent=2) + "\n")
        temporary.replace(receipt)

    save()
    lock = None
    child_env = dict(os.environ)
    for key in ("LEAN_PATH", "LEAN_SRC_PATH", "LEAN_SYSROOT"):
        child_env.pop(key, None)

    def run(label: str, command: list[str], cwd: Path = root) -> str:
        require(lock is not None, "Compiler commands require the maintained shared lock")
        log = logs / f"{len(status['commands']):02d}-{label}.log"
        row = {"label": label, "command": command, "cwd": str(cwd),
               "log": str(log), "exit_code": None, "status": "launching"}
        status["commands"].append(row)
        status["status"] = label
        save()
        print(f"[summable-compatible] {label}: {' '.join(command)}", flush=True)
        process = None
        started = time.monotonic()
        try:
            with log.open("w") as stream:
                try:
                    process = subprocess.Popen(
                        command, cwd=cwd, env=child_env, stdin=subprocess.DEVNULL,
                        stdout=stream, stderr=subprocess.STDOUT,
                        start_new_session=(os.name == "posix"),
                        pass_fds=(lock.fileno(),) if os.name == "posix" else (),
                    )
                    row.update(status="running", pid=process.pid)
                    save()
                    process.wait()
                finally:
                    if process is not None and process.poll() is None:
                        _interrupt_child_and_wait(process)
        finally:
            row["exit_code"] = process.returncode if process is not None else None
            row["status"] = "exited" if process is not None else "launch_failed"
            row["elapsed_seconds"] = round(time.monotonic() - started, 3)
            save()
        text = log.read_text(errors="replace")
        if row["exit_code"] != 0:
            print(text, flush=True)
            raise RuntimeError(f"{label} failed with exit {row['exit_code']}; see {log}")
        return text

    try:
        print("[summable-compatible] waiting for the maintained shared build lock", flush=True)
        lock = acquire_build_lock(None, f"summable-compatible-functionals:{os.getpid()}", block=not args.no_wait)
        print("[summable-compatible] acquired the shared lock", flush=True)
        require({str(p): digest(p) for p in controls} == control_hashes,
                "Pins or verification controls changed before the build lock was acquired")
        status["lock_acquired_at"] = datetime.now(timezone.utc).isoformat()
        save()
        modules, repository_imports, native_imports = closure(root, owners)
        sources = {m: root / "lean" / (m.replace(".", "/") + ".lean") for m in modules}
        source_hashes = {m: digest(p) for m, p in sources.items()}
        status.update(repository_modules=modules, repository_imports=repository_imports,
                      direct_mathlib_imports=sorted(native_imports),
                      source_sha256=source_hashes, control_sha256=control_hashes)
        status["git_head"] = run("repository-head", ["git", "rev-parse", "HEAD"]).strip()
        toolchain_bytes = (root / "lean-toolchain").read_bytes()
        require(toolchain_bytes == (root / "verification/real-matrix-split/lean-toolchain").read_bytes(),
                "Root and maintained focused toolchain differ")
        toolchain = toolchain_bytes.decode().strip()
        version_match = re.fullmatch(r"leanprover/lean4:v([0-9]+\.[0-9]+\.[0-9]+)", toolchain)
        require(version_match is not None, "Expected a fixed released Lean version")
        version = version_match.group(1)
        child_env["ELAN_TOOLCHAIN"] = toolchain
        status["toolchain"] = toolchain
        root_manifest = json.loads((root / "lake-manifest.json").read_text())
        manifest = json.loads((root / "verification/real-matrix-split/lake-manifest.json").read_text())
        root_pins = {p["name"]: p["rev"] for p in root_manifest["packages"] if p["type"] == "git"}
        packages = manifest["packages"]
        require(len({p["name"] for p in packages}) == len(packages), "Duplicate package name")
        for package in packages:
            require(package["type"] == "git", "Expected only pinned Git dependencies")
            require(bool(re.fullmatch(r"[0-9a-f]{40}", package["rev"])), "Nonimmutable revision")
            require(root_pins.get(package["name"]) == package["rev"], "Focused/root pin mismatch")

        def dependencies(prefix: str) -> dict[str, str]:
            observed = {}
            for package in packages:
                name, revision = package["name"], package["rev"]
                directory = package_root / name
                require(directory.is_dir(), f"Missing exact-pin dependency {name}")
                actual = run(f"{prefix}-{name}-head", ["git", "rev-parse", "HEAD"], directory).strip()
                require(actual == revision, f"Dependency {name} differs from its fixed pin")
                run(f"{prefix}-{name}-clean", ["git", "diff", "--exit-code", "HEAD", "--"], directory)
                untracked = run(f"{prefix}-{name}-untracked", [
                    "git", "ls-files", "--others", "--exclude-standard", "--", "*.lean",
                    "lean-toolchain", "lakefile.lean", "lakefile.toml", "lake-manifest.json"], directory)
                require(not untracked.strip(), f"Untracked dependency source/configuration: {name}")
                observed[name] = actual
            return observed

        pins = dependencies("before")
        require((package_root / "mathlib/lean-toolchain").read_bytes() == toolchain_bytes,
                "Mathlib toolchain differs from repository toolchain")
        status["dependency_pins"] = pins
        status["lake_executable"] = shutil.which("lake")
        status["lean_executable"] = shutil.which("lean")
        require(status["lake_executable"] is not None and status["lean_executable"] is not None,
                "Put the pinned Lean runtime bin directory on PATH")
        (work / "lean-toolchain").write_bytes(toolchain_bytes)
        manifest["name"] = "summable_compatibility_validation"
        manifest["packagesDir"] = ".lake/packages"
        (work / "lake-manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
        (work / "lakefile.toml").write_text(
            'name = "summable_compatibility_validation"\nsrcDir = "src"\n'
            'packagesDir = ".lake/packages"\n\n[[require]]\nname = "mathlib"\n'
            'git = "https://github.com/leanprover-community/mathlib4.git"\n'
            f'rev = "{pins["mathlib"]}"\n\n[[lean_lib]]\nname = "InfoGeometry"\n')
        overrides = [{"type": "path", "scope": p.get("scope", ""), "name": p["name"],
                      "dir": str(package_root / p["name"]), "inherited": p.get("inherited", False),
                      "manifestFile": p["manifestFile"], "configFile": p["configFile"]} for p in packages]
        override_path = work / "package-overrides.json"
        override_path.write_text(json.dumps({"version": manifest["version"], "packages": overrides}, indent=2) + "\n")
        project_hashes = {str(p): digest(p) for p in (
            work / "lean-toolchain", work / "lake-manifest.json", work / "lakefile.toml", override_path)}
        for module, source in sources.items():
            target = work / "src" / (module.replace(".", "/") + ".lean")
            target.parent.mkdir(parents=True, exist_ok=True)
            if not target.is_file() or digest(target) != source_hashes[module]:
                shutil.copyfile(source, target)
            require(digest(target) == source_hashes[module], f"Copied source mismatch: {module}")
        lake = ["lake", "-d", str(work), f"--packages={override_path}"]
        def runtime_identity(prefix: str) -> dict[str, str]:
            lake_banner = run(prefix + "-lake-version", ["lake", "--version"]).strip()
            require(f"Lean version {version})" in lake_banner,
                    "Lake runtime version differs from pin")
            run(prefix + "-runtime-self-check", ["lake", "self-check"])
            # Print only compiler locations, never the complete Lake environment.
            probe = ("import json, os; print(json.dumps({k: os.environ.get(k) "
                     "for k in ('LEAN', 'LAKE', 'LEAN_SYSROOT')}))")
            settings = json.loads(run(prefix + "-runtime-paths",
                                      lake + ["env", sys.executable, "-c", probe]))
            require(all(settings.get(k) for k in ("LEAN", "LAKE", "LEAN_SYSROOT")),
                    "Lake did not report its actual Lean/Lake installation")
            lean_path = Path(settings["LEAN"]).resolve()
            lake_path = Path(settings["LAKE"]).resolve()
            runtime_root = Path(settings["LEAN_SYSROOT"]).resolve()
            require(lean_path == (runtime_root / "bin/lean").resolve() and
                    lake_path == (runtime_root / "bin/lake").resolve(),
                    "Selected Lean and Lake do not belong to the same runtime")
            lean_banner = run(prefix + "-lean-version", [str(lean_path), "--version"]).strip()
            require(bool(re.search(r"\bversion\s+" + re.escape(version) + r"(?=[,\s)])", lean_banner)),
                    "Resolved Lean runtime version differs from pin")
            actual_root = run(prefix + "-lean-prefix", [str(lean_path), "--print-prefix"]).strip()
            require(Path(actual_root).resolve() == runtime_root,
                    "Lean's actual prefix differs from Lake's installation")
            return {"lake": str(lake_path), "lean": str(lean_path),
                    "root": str(runtime_root), "lake_version": lake_banner,
                    "lean_version": lean_banner, "lake_sha256": digest(lake_path),
                    "lean_sha256": digest(lean_path)}

        runtime = runtime_identity("before")
        status.update(runtime=runtime, project_sha256=project_hashes)
        if args.phase in ("build", "audit", "final"):
            # Explicitly ordered closure keeps repository owner builds serial;
            # exact native dependency caches remain in the package directory.
            for module in modules:
                run("build-" + module, lake + ["build", module])
        if args.phase == "final":
            for module in owners:
                copied = work / "src" / (module.replace(".", "/") + ".lean")
                run("fresh-" + module, lake + ["env", "lean", "-DwarningAsError=true", str(copied)])
        if args.phase in ("audit", "final"):
            audit = logs / "OwnedDeclarationsAudit.lean"
            audit.write_text(audit_source(owners))
            audit_hash = digest(audit)
            evidence = run("axioms", lake + ["env", "lean", "-DwarningAsError=true", str(audit)])
            require(digest(audit) == audit_hash, "Generated audit source changed during execution")
            counts = parse_audit_output(evidence, owners)
            status["owner_declaration_counts"] = counts
            status["audited_declaration_count"] = sum(counts.values())
            status["audit_source_sha256"] = audit_hash
            status["audit_axiom_markers"] = [line for line in evidence.splitlines() if line.startswith("AUDIT_AXIOMS:")]
        require(closure(root, owners)[0] == modules, "Repository import closure changed during verification")
        require({m: digest(p) for m, p in sources.items()} == source_hashes,
                "Repository source changed during verification")
        require({m: digest(work / 'src' / (m.replace('.', '/') + '.lean')) for m in modules} == source_hashes,
                "Copied source changed during verification")
        require({str(p): digest(p) for p in controls} == control_hashes,
                "Pins or verification controls changed during verification")
        require({p: digest(Path(p)) for p in project_hashes} == project_hashes,
                "Isolated project configuration changed during verification")
        require(dependencies("after") == pins, "Dependencies changed during verification")
        require(runtime_identity("after") == runtime, "Selected runtime changed during verification")
        require(run("repository-head-final", ["git", "rev-parse", "HEAD"]).strip() == status["git_head"],
                "Repository commit changed during verification")
        status["status"] = {"build": "build_passed", "audit": "audit_passed", "final": "focused_passed"}[args.phase]
        status["completed_at"] = datetime.now(timezone.utc).isoformat()
        save()
        print(f"[summable-compatible] {status['status']}; exact-source receipt: {receipt}", flush=True)
        return 0
    except BaseException as error:
        status["status"] = "interrupted" if isinstance(error, KeyboardInterrupt) else "failed"
        status["error"] = str(error)
        save()
        raise
    finally:
        if lock is not None:
            lock.release()


if __name__ == "__main__":
    raise SystemExit(main())
