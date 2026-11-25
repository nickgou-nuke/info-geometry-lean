#!/usr/bin/env python3
"""Collect nonaccepting native diagnostics after a failed strict full-suite run.

Intended location: verification/witt-born-null-exactness/diagnose.py.
This script always exits nonzero. Its outputs never establish acceptance and
are never loaded from or copied into either strict suite's compilation cache.
"""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import sys
import uuid

SCRIPT = Path(__file__).resolve()
SCRIPT_HASH = hashlib.sha256(SCRIPT.read_bytes()).hexdigest()
ROOT = SCRIPT.parents[2]
SUITE = "witt-born-null-exactness"
sys.path.insert(0, str(ROOT))
from tools.build_lock import BuildLock, BuildLockBusyError, DEFAULT_BUILD_LOCK_PATH

spec = importlib.util.spec_from_file_location(
    "strict_zorn_checker", ROOT / "verification/zorn-primal-dual/check.py")
checker = importlib.util.module_from_spec(spec)
spec.loader.exec_module(checker)


class DiagnosticParser(argparse.ArgumentParser):
    def exit(self, status=0, message=None):
        super().exit(status or 2, message)


def run(args: argparse.Namespace, out: Path, report: dict) -> int:
    strict_path = ROOT / ".lake" / SUITE / "report.json"
    strict_bytes = strict_path.read_bytes()
    strict = json.loads(strict_bytes)
    targets = checker.SUITES[SUITE]
    if (strict.get("suite") != SUITE or strict.get("status") != "failed"
            or not strict.get("audit_expected")
            or strict.get("audit_status") != "not-run"
            or set(strict.get("targets", [])) != set(targets)):
        raise RuntimeError("A failed complete strict-suite compilation receipt is required")
    commands = strict.get("commands", [])
    if not commands or commands[-1].get("returncode", 0) <= 0:
        raise RuntimeError("No completed nonsignal strict compiler failure to diagnose")
    error = checker._validate_lake_workspace_integrity(ROOT)
    if error:
        raise RuntimeError(error)
    lib = out / "lib/lean"
    lib.mkdir(parents=True, exist_ok=False)
    if not lib.resolve().is_relative_to(out.resolve()):
        raise RuntimeError("Diagnostic library escaped its fresh run directory")
    fingerprint, paths = checker.environment(args, lib)
    if any(strict.get(key) != value for key, value in fingerprint.items()):
        raise RuntimeError("Strict receipt and current compiler/dependency/verifier identity differ")
    report.update(environment={**fingerprint, "owned_warning_as_error": False},
                  strict_receipt_sha256=hashlib.sha256(strict_bytes).hexdigest(),
                  strict_run_id=strict["run_id"], targets=targets)
    env = os.environ.copy()
    env["LEAN_PATH"] = os.pathsep.join(map(str, paths))
    env.pop("LEAN_SRC_PATH", None)
    with BuildLock(DEFAULT_BUILD_LOCK_PATH, f"zorn-diagnostics:{os.getpid()}",
                   block=False, shared=False) as lock:
        if (checker.digest(SCRIPT) != SCRIPT_HASH
                or checker.digest(checker.CHECKER) != checker.STARTUP_CHECKER_HASH):
            raise RuntimeError("Diagnostic or strict checker source changed before compilation")
        if strict_path.read_bytes() != strict_bytes:
            raise RuntimeError("Strict receipt changed before diagnostic compilation")
        if checker.environment(args, lib) != (fingerprint, paths):
            raise RuntimeError("Native environment changed before diagnostic compilation")
        modules = checker.closure(targets)
        sources = {m: checker.digest(checker.source(m)) for m in modules}
        if modules != strict.get("modules") or sources != strict.get("sources"):
            raise RuntimeError("Diagnostic closure differs from the failed strict source snapshot")
        audit_file = ROOT / "verification" / SUITE / "Audit.lean"
        if checker.digest(audit_file) != strict.get("audit_sha256"):
            raise RuntimeError("Strict audit source changed")
        report.update(modules=modules, sources=sources, status="diagnostic-running")
        checker.receipt(out, report)
        states: dict[str, str] = {}
        for module in modules:
            dependencies = [d for d in checker.dependencies(module)
                            if d.startswith("InfoGeometry.")]
            blocked = [d for d in dependencies if states.get(d) != "elaborated"]
            if blocked:
                states[module] = "skipped"
                report["results"].append({"module": module, "status": "skipped",
                                          "blocked_by": blocked})
                print(f"[diagnostic skipped] {module}: {', '.join(blocked)}", flush=True)
                checker.receipt(out, report)
                continue
            if checker.digest(checker.source(module)) != sources[module]:
                raise RuntimeError(f"Source changed during diagnostics: {module}")
            dest = lib / Path(module.replace(".", "/")).with_suffix(".olean")
            dest.parent.mkdir(parents=True, exist_ok=True)
            command = [str(args.lean), "-j1", "-R", str(ROOT / "lean"),
                       str(checker.source(module)), "-o", str(dest),
                       "-DwarningAsError=false"]
            print(f"[nonaccepting diagnostic] {module}", flush=True)
            result = checker.execute(command, env, out / f"{module}.log", lock.fileno())
            state = "elaborated" if result["returncode"] == 0 else "error"
            states[module] = state
            report["results"].append({"module": module, "status": state, **result})
            checker.receipt(out, report)
            if result["returncode"] < 0:
                raise RuntimeError("Diagnostic compiler terminated by a signal; stopping")
        for module in modules:
            if checker.digest(checker.source(module)) != sources[module]:
                raise RuntimeError(f"Source changed during diagnostics: {module}")
        if (checker.digest(SCRIPT) != SCRIPT_HASH
                or checker.digest(checker.CHECKER) != checker.STARTUP_CHECKER_HASH
                or checker.digest(audit_file) != strict["audit_sha256"]
                or strict_path.read_bytes() != strict_bytes
                or checker.environment(args, lib) != (fingerprint, paths)):
            raise RuntimeError("Diagnostic inputs changed during the run")
        report.update(status="diagnostic-complete",
                      error_modules=[m for m, state in states.items() if state == "error"],
                      skipped_modules=[m for m, state in states.items() if state == "skipped"])
    print("Diagnostics complete; acceptance remains false and the strict run remains failed.",
          flush=True)
    return 2


def main() -> int:
    parser = DiagnosticParser(description=__doc__)
    parser.add_argument("--lean", type=Path, required=True)
    parser.add_argument("--packages", type=Path, required=True)
    args = parser.parse_args()
    error = checker._validate_lake_workspace_integrity(ROOT)
    if error:
        parser.error(error)
    diagnostic_root = ROOT / ".lake/witt-born-diagnostics"
    if diagnostic_root.is_symlink():
        parser.error("The diagnostic output root must not be a symlink")
    run_id = uuid.uuid4().hex
    out = diagnostic_root / run_id
    out.mkdir(parents=True, exist_ok=False)
    report = {"run_id": run_id, "status": "diagnostic-starting", "acceptance": False,
              "audit_status": "not-run-diagnostic-only", "results": [],
              "diagnostic_script_sha256": SCRIPT_HASH,
              "started_at": datetime.now(timezone.utc).isoformat()}
    checker.receipt(out, report)
    try:
        return run(args, out, report)
    except BuildLockBusyError as error:
        report.update(status="diagnostic-blocked", error=str(error), build_lock=error.metadata)
        return 2
    except KeyboardInterrupt:
        report.update(status="diagnostic-interrupted", error="KeyboardInterrupt")
        return 130
    except Exception as error:
        report.update(status="diagnostic-error", error=f"{type(error).__name__}: {error}")
        print(report["error"], file=sys.stderr, flush=True)
        return 1
    finally:
        report["finished_at"] = datetime.now(timezone.utc).isoformat()
        checker.receipt(out, report)


if __name__ == "__main__":
    raise SystemExit(main())
