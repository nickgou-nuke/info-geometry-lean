#!/usr/bin/env python3
"""Compile the selected source closure and audit it with pinned native Lean.

An existing pinned dependency cache is read without modifying it. All outputs
belong to this independent checkout. Native compilation and the axiom audit
run sequentially under the repository's maintained exclusive build lock.
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
import signal
import subprocess
import sys
import time
import uuid

CHECKER = Path(__file__).resolve()
STARTUP_CHECKER_HASH = hashlib.sha256(CHECKER.read_bytes()).hexdigest()
ROOT = CHECKER.parents[2]
sys.path.insert(0, str(ROOT))
from tools.build_lock import BuildLockBusyError, acquire_build_lock
from tools.infra.build import _validate_lake_workspace_integrity

NEW_TARGETS = [
    "InfoGeometry.Algebra.ZornPrimalDual",
    "InfoGeometry.Algebra.ZornChiralOperatorReconstruction",
    "InfoGeometry.Canonical.SouriauAffineActionGroupoid",
    "InfoGeometry.Geometry.SouriauCotangentGraphSigns",
]
TARGETS = [*NEW_TARGETS, "InfoGeometry.Lie.SplitOctonionCliffordNoninjective"]
KLEIN_TARGETS = [
    "InfoGeometry.Algebra.ZornNullIncidence",
    "InfoGeometry.Canonical.ZornCliffordKleinHierarchy",
    "InfoGeometry.Canonical.ZornCliffordSourceVolume",
    "InfoGeometry.Lie.SplitOctonionNullPlaneCovariance",
]
OWNED = [
    "InfoGeometry.Algebra.ZornLeftInverse",
    "InfoGeometry.Algebra.ZornLeftDeterminant",
    *NEW_TARGETS,
    *KLEIN_TARGETS,
]
SUITES = {"zorn-primal-dual": TARGETS, "klein-operator-hierarchy": KLEIN_TARGETS}
PIN = "d13f23b723b8a846827a245b89c10fc7d3f11612"


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def source(module: str) -> Path:
    return ROOT / "lean" / Path(module.replace(".", "/")).with_suffix(".lean")


def dependencies(module: str) -> list[str]:
    return re.findall(r"^import\s+([\w.]+)", source(module).read_text(), re.M)


def closure(targets: list[str]) -> list[str]:
    seen: set[str] = set()
    ordered: list[str] = []
    def visit(module: str) -> None:
        if module in seen:
            return
        seen.add(module)
        for dependency in dependencies(module):
            if dependency.startswith("InfoGeometry."):
                visit(dependency)
            elif dependency.split(".")[0] not in {"Mathlib", "Lean", "Batteries", "Std", "Qq", "Aesop"}:
                raise RuntimeError(f"unexpected import in {module}: {dependency}")
        ordered.append(module)
    for module in targets:
        visit(module)
    return ordered


def receipt(out: Path, report: dict) -> None:
    text = json.dumps(report, indent=2) + "\n"
    (out / f"report-{report['run_id']}.json").write_text(text)
    pending = out / "report.json.tmp"
    pending.write_text(text)
    pending.replace(out / "report.json")


def environment(args: argparse.Namespace, lib: Path) -> tuple[dict, list[Path]]:
    packages = args.packages.resolve()
    version = subprocess.check_output([args.lean, "--version"], text=True).strip()
    if not re.search(r"version 4\.34\.1[,)]", version):
        raise RuntimeError(f"wrong toolchain: {version}")
    manifest = json.loads((ROOT / "lake-manifest.json").read_text())
    expected = {p["name"]: p["rev"] for p in manifest["packages"] if p["type"] == "git"}
    paths = [lib] + sorted(p for p in packages.glob("*/.lake/build/lib/lean") if p.is_dir())
    if any((p / "InfoGeometry").exists() for p in paths[1:]):
        raise RuntimeError("dependency cache shadows the repository namespace")
    resolved_packages = {}
    for path in paths[1:]:
        name = path.relative_to(packages).parts[0]
        package = packages / name
        revision = subprocess.check_output(["git", "-C", str(package), "rev-parse", "HEAD"],
                                           text=True).strip()
        dirty = subprocess.check_output(["git", "-C", str(package), "status", "--porcelain",
                                         "--untracked-files=no"], text=True).strip()
        if revision != expected.get(name) or dirty:
            raise RuntimeError(f"dependency does not match its pinned source: {name}")
        resolved_packages[name] = {"revision": revision, "search_path": str(path)}
    if resolved_packages.get("mathlib", {}).get("revision") != PIN:
        raise RuntimeError("Mathlib is absent or at the wrong revision")
    fingerprint = {"lean": version, "lean_binary_sha256": digest(Path(args.lean).resolve()),
                   "packages": resolved_packages, "manifest_sha256": digest(ROOT / "lake-manifest.json"),
                   "verifier_sha256": STARTUP_CHECKER_HASH,
                   "owned_warning_as_error": True, "lean_threads": 1}
    return fingerprint, paths


def execute(command: list[str], env: dict, logfile: Path, lock_fd: int) -> dict:
    started = time.monotonic()
    peak_rss_kib = 0
    with logfile.open("w") as output:
        proc = subprocess.Popen(command, env=env, cwd=ROOT, text=True,
                                stdout=output, stderr=subprocess.STDOUT, pass_fds=(lock_fd,))
        try:
            while True:
                try:
                    returncode = proc.wait(timeout=30)
                    break
                except subprocess.TimeoutExpired:
                    status_file = Path(f"/proc/{proc.pid}/status")
                    try:
                        status = status_file.read_text()
                    except (FileNotFoundError, ProcessLookupError):
                        status = ""
                    match = re.search(r"^VmHWM:\s+(\d+)\s+kB", status, re.M)
                    if match:
                        peak_rss_kib = max(peak_rss_kib, int(match[1]))
                    print(f"[running] {int(time.monotonic() - started)}s; "
                          f"peak RSS {peak_rss_kib // 1024} MiB; log {logfile.name}", flush=True)
        except BaseException:
            # Reap only this invocation's child before releasing its build lock.
            # A second Ctrl-C must not interrupt the short cleanup and leave an
            # active compiler behind an explicitly unlocked descriptor.
            previous_sigint = signal.signal(signal.SIGINT, signal.SIG_IGN)
            try:
                if proc.poll() is None:
                    proc.terminate()
                    try:
                        proc.wait(timeout=10)
                    except subprocess.TimeoutExpired:
                        proc.kill()
                        proc.wait()
            finally:
                signal.signal(signal.SIGINT, previous_sigint)
            raise
    text = logfile.read_text()
    print(text, end="", flush=True)
    return {"command": command, "returncode": returncode, "output": text,
            "elapsed_seconds": round(time.monotonic() - started, 3),
            "sampled_peak_rss_kib": peak_rss_kib}


def run(args: argparse.Namespace, out: Path, report: dict) -> int:
    error = _validate_lake_workspace_integrity(ROOT)
    if error:
        raise RuntimeError(error)
    lib = out / "lib/lean"
    lib.mkdir(parents=True, exist_ok=True)
    fingerprint, paths = environment(args, lib)
    report.update(fingerprint)
    report["mathlib"] = PIN
    receipt(out, report)
    env = os.environ.copy()
    env["LEAN_PATH"] = os.pathsep.join(map(str, paths))
    env.pop("LEAN_SRC_PATH", None)
    print(f"[{args.suite}] acquiring shared build lock", flush=True)
    with acquire_build_lock(None, f"{args.suite}:{os.getpid()}", block=args.wait) as lock:
        if digest(CHECKER) != STARTUP_CHECKER_HASH:
            raise RuntimeError("verifier changed while waiting; restart this invocation")
        if environment(args, lib) != (fingerprint, paths):
            raise RuntimeError("compiler or dependency environment changed while waiting")
        modules = closure(args.targets)
        sources = {m: digest(source(m)) for m in modules}
        audit_file = ROOT / "verification" / args.suite / "Audit.lean"
        audit_hash = digest(audit_file)
        previous_file = out / "compiled.json"
        previous = json.loads(previous_file.read_text()) if previous_file.exists() else {}
        compiled = dict(previous.get("sources", {})) if previous.get("environment") == fingerprint else {}
        report.update(modules=modules, sources=sources, audit_sha256=audit_hash, commands=[], status="running")
        receipt(out, report)
        print(f"[{args.suite}] checking {len(modules)} repository modules", flush=True)
        for module in modules:
            dest = lib / Path(module.replace(".", "/")).with_suffix(".olean")
            dep_outputs = [lib / Path(d.replace(".", "/")).with_suffix(".olean")
                           for d in dependencies(module) if d.startswith("InfoGeometry.")]
            fresh = (dest.exists() and compiled.get(module) == sources[module]
                     and all(d.exists() and d.stat().st_mtime <= dest.stat().st_mtime for d in dep_outputs))
            if fresh and not args.force:
                print(f"[cached] {module}", flush=True)
                continue
            dest.parent.mkdir(parents=True, exist_ok=True)
            if digest(source(module)) != sources[module]:
                raise RuntimeError(f"source changed during compilation: {module}")
            command = [str(args.lean), "-j1", "-R", str(ROOT / "lean"), str(source(module)), "-o", str(dest)]
            if module in OWNED:
                command.append("-DwarningAsError=true")
            print(f"[compile] {module}", flush=True)
            result = execute(command, env, out / f"{module}.log", lock.fileno())
            report["commands"].append({"module": module, **result})
            if result["returncode"]:
                report["status"] = "failed"
                return result["returncode"]
            if digest(source(module)) != sources[module]:
                raise RuntimeError(f"source changed during compilation: {module}")
            compiled[module] = sources[module]
            previous_file.write_text(json.dumps({"sources": compiled, "environment": fingerprint}, indent=2) + "\n")
            receipt(out, report)
        if report["audit_expected"]:
            command = [str(args.lean), "-j1", str(audit_file), "-DwarningAsError=true"]
            print(f"[audit] {audit_file.relative_to(ROOT)}", flush=True)
            report["audit_status"] = "running"
            receipt(out, report)
            result = execute(command, env, out / "Audit.log", lock.fileno())
            report["audit"] = result
            if result["returncode"]:
                report["audit_status"] = "failed"
                report["status"] = "audit-failed"
                return result["returncode"]
            report["audit_status"] = "passed"
        for module in modules:
            if digest(source(module)) != sources[module]:
                raise RuntimeError(f"source changed during validation: {module}")
        if digest(CHECKER) != STARTUP_CHECKER_HASH:
            raise RuntimeError("verifier changed during validation")
        if digest(audit_file) != audit_hash:
            raise RuntimeError("audit changed during validation")
        if digest(ROOT / "lake-manifest.json") != fingerprint["manifest_sha256"]:
            raise RuntimeError("dependency manifest changed during validation")
        if environment(args, lib) != (fingerprint, paths):
            raise RuntimeError("compiler or dependency environment changed during validation")
        report["status"] = "compiled"
    print(f"[{args.suite}] compiled {len(modules)} modules", flush=True)
    return 0


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lean", default=shutil.which("lean"))
    parser.add_argument("--packages", type=Path, default=ROOT / ".lake/packages")
    parser.add_argument("--force", action="store_true", help="recompile unchanged source closure")
    parser.add_argument("--suite", choices=SUITES, default="zorn-primal-dual")
    parser.add_argument("--targets", nargs="+", help="override the selected suite's targets")
    parser.add_argument("--no-wait-for-build-lock", dest="wait", action="store_false",
                        default=True, help="record a blocked result if another build holds the lock")
    args = parser.parse_args()
    if args.targets is None:
        args.targets = SUITES[args.suite]
    audit_expected = set(args.targets) == set(SUITES[args.suite])
    if not args.lean:
        parser.error("provide the pinned Lean executable with --lean")
    out = ROOT / ".lake" / args.suite
    out.mkdir(parents=True, exist_ok=True)
    report = {"run_id": uuid.uuid4().hex, "status": "running", "suite": args.suite,
              "targets": args.targets, "wait_for_build_lock": args.wait,
              "commands": [], "audit_expected": audit_expected,
              "audit_status": "not-run" if audit_expected else "not-selected",
              "force": args.force, "started_at": datetime.now(timezone.utc).isoformat(),
              "verifier_sha256": STARTUP_CHECKER_HASH}
    receipt(out, report)
    try:
        return run(args, out, report)
    except BuildLockBusyError as error:
        report.update(status="blocked", error=str(error), build_lock=error.metadata)
        print(report["error"], file=sys.stderr, flush=True)
        return 2
    except KeyboardInterrupt:
        report.update(status="interrupted", error="KeyboardInterrupt")
        return 130
    except Exception as error:
        report.update(status="failed", error=f"{type(error).__name__}: {error}")
        print(report["error"], file=sys.stderr, flush=True)
        return 1
    finally:
        report["finished_at"] = datetime.now(timezone.utc).isoformat()
        receipt(out, report)


if __name__ == "__main__":
    raise SystemExit(main())
