#!/usr/bin/env python3
"""Native, serialized runtime and generated route-certificate acceptance."""
from __future__ import annotations

import argparse
from contextlib import redirect_stdout, redirect_stderr
import traceback
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import unittest

TARGET = "InfoGeometry.Routing.FunctionalRouteCertificate"
SUITES = (
    "attention_polytope", "certified_caratheodory", "functional_route_fibers", "route_certificate",
    "route_diagnostics_torch", "shape_sinkhorn_detector", "causal_bipartite_sinkhorn",
)
FIXTURES = (
    [0], [1, 0], [1, 2, 0], [0, 0], [0, 0, 1, 1], [0, 0, 1, 2],
    [1, 2, 0, 2, 3, 4], [1, 0, 0, 2, 5, 4, 5, 6],
)
HEADS = ("local_certificate", "certified_inverse", "certified_minimum")


def require(ok: bool, message: str) -> None:
    if not ok:
        raise RuntimeError(message)


def native_lean_sources(root: Path) -> list[Path]:
    """Tracked and nonignored untracked Lean files, not checkout completeness."""
    inventory = subprocess.check_output(
        ["git", "ls-files", "--cached", "--others", "--exclude-standard",
         "-z", "--", "lean"], cwd=root).decode().split("\0")
    return sorted({root / name for name in inventory if name.endswith(".lean")
                   and (root / name).is_file()})


def idle() -> None:
    """Fail closed on uncoordinated compiler/test processes; never kill them."""
    rows = subprocess.check_output(["ps", "-eo", "pid=,comm=,args="], text=True)
    busy = []
    for row in rows.splitlines():
        fields = row.strip().split(None, 2)
        if len(fields) < 2:
            continue
        pid, comm = fields[:2]
        args = fields[2] if len(fields) == 3 else ""
        if int(pid) == os.getpid():
            continue
        if comm in {"lean", "lake", "leanc", "clang", "gcc", "cc1", "pytest",
                    "cargo", "rustc", "ninja", "make"} or re.search(
            r"\bpython\S*\s+(?:-m\s+(?:pytest|unittest)|\S*/test_[^ ]+\.py)(?:\s|$)", args
        ):
            busy.append(row)
    require(not busy, "Active compiler/test processes:\n" + "\n".join(busy))


def audit(text: str, namespace: str) -> None:
    """Require exactly the three named footprints, not just three messages."""
    records = re.findall(
        r"'([^']+)'\s+(?:depends on axioms:\s*\[([^\]]*)\]|"
        r"(does not depend on any axioms))", text, re.S
    )
    names = [name.replace("«", "").replace("»", "") for name, _, _ in records]
    require(sorted(names) == sorted(f"{namespace}.{h}" for h in HEADS),
            f"Missing/extra axiom footprints: {names}")
    for _, axioms, _ in records:
        require({s.strip() for s in axioms.split(",") if s.strip()} <=
                {"propext", "Classical.choice", "Quot.sound"}, f"Forbidden axioms: {axioms}")
    require(not re.search(r"\b(?:warning|error):", text), "Generated Lean diagnostic")


def runtime_suites(root: Path, out: Path) -> list[dict]:
    rows = []
    for name in SUITES:
        loader = unittest.TestLoader()
        with (out / f"test_{name}.log").open("w") as stream:
            with redirect_stdout(stream), redirect_stderr(stream):
                try:
                    suite = loader.discover(str(root / "tests"), pattern=f"test_{name}.py")
                    collected = suite.countTestCases()
                    result = unittest.TextTestRunner(stream=stream, verbosity=2).run(suite)
                except BaseException:
                    traceback.print_exc(file=stream)
                    raise
        row = dict(suite=name, collected=collected, ran=result.testsRun,
                   skipped=len(result.skipped), failures=len(result.failures),
                   errors=len(result.errors), expected_failures=len(result.expectedFailures),
                   unexpected_successes=len(result.unexpectedSuccesses))
        rows.append(row)
        (out / "runtime-tests.json").write_text(json.dumps(rows, indent=2) + "\n")
        require(not loader.errors and collected > 0 and result.testsRun == collected
                and result.wasSuccessful() and not result.skipped
                and not result.expectedFailures and not result.unexpectedSuccesses,
                f"Incomplete/failed runtime suite: {row}")
    return rows


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=Path.cwd())
    parser.add_argument("--wait-for-build-lock", action="store_true",
                        help="Queue behind an existing shared verification job")
    parser.add_argument("--out", type=Path, required=True,
                        help="Fresh artifact directory inside the native repository")
    args = parser.parse_args()
    root = args.root.resolve()
    os.chdir(root)
    out = (root / args.out).resolve()
    require(out.is_relative_to(root) and out != root, "Output must be inside the repository")
    out.mkdir(parents=True, exist_ok=False)
    sys.path.insert(0, str(root))
    status = {"result": "failed", "scope": "Seven runtime suites and eight emitted finite certificates"}
    try:
        from tools.build_lock import BuildLock, DEFAULT_BUILD_LOCK_PATH
        from tools.infra.ci_bootstrap import path_package_report, verify_version
        from tools.infra.build import lake_build_command

        # A busy lane either rejects or queues; neither mode permits overlap.
        with BuildLock(DEFAULT_BUILD_LOCK_PATH, "native-runtime-acceptance",
                       block=args.wait_for_build_lock) as lock:
            idle()

            def run(label: str, command: list[str], *, success: bool = True,
                    stdout_only: bool = False):
                idle()
                try:
                    process = subprocess.Popen(command, cwd=root, text=True,
                        stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                        pass_fds=(lock.fileno(),), start_new_session=True)
                except BaseException:
                    (out / f"{label}.log").write_text(traceback.format_exc())
                    raise
                interrupted = False
                while True:
                    try:
                        stdout, stderr = process.communicate()
                        break
                    except KeyboardInterrupt:
                        # Retain the shared lock and wait; do not kill a Lean task.
                        interrupted = True
                text = stdout + stderr
                (out / f"{label}.log").write_text(text)
                (out / f"{label}.stdout.log").write_text(stdout)
                (out / f"{label}.stderr.log").write_text(stderr)
                if interrupted:
                    raise KeyboardInterrupt
                if success:
                    require(process.returncode == 0, f"{label} failed; see {label}.log")
                return process.returncode, stdout if stdout_only else text

            def snapshot() -> dict[str, str]:
                # Native tracked/nonignored sources, excluding nested worktrees
                # and caches. A directory may itself have a .lean suffix.
                paths = native_lean_sources(root)
                paths += [root / "tools" / f"{s}.py" for s in SUITES]
                paths += [root / "tests" / f"test_{s}.py" for s in SUITES]
                paths += [root / p for p in ("lean-toolchain", "lakefile.lean", "lake-manifest.json",
                    ".gitmodules", "tools/build_lock.py", "tools/infra/build.py",
                    "tools/infra/ci_bootstrap.py")]
                paths += [Path(__file__).resolve()]
                return {str(p.relative_to(root)): hashlib.sha256(p.read_bytes()).hexdigest()
                        for p in sorted(set(paths))}

            before = snapshot()
            (out / "source-sha256.json").write_text(json.dumps(before, indent=2) + "\n")
            _, revision = run("revision", ["git", "rev-parse", "HEAD"])
            run("git-status", ["git", "status", "--porcelain=v1", "--untracked-files=normal"])
            status["source_commit"] = revision.strip()
            paths = path_package_report(root)
            (out / "path-dependencies.json").write_text(json.dumps(paths, indent=2) + "\n")
            require(paths["ok"], "Native ci_bootstrap path preflight failed")
            # Lake may emit dependency warnings on stderr before Lean's banner.
            # Preserve those diagnostics, but parse the actual stdout banner.
            _, banner = run("lean-version", ["lake", "env", "lean", "--version"],
                            stdout_only=True)
            status["lean"] = verify_version((root / "lean-toolchain").read_text(), banner)
            # Explicit dependency failure, not optional Torch skips.
            import torch
            status.update(python=sys.version, torch=torch.__version__)
            idle()
            rows = runtime_suites(root, out)
            status["runtime_suites"] = rows
            status["runtime_test_count"] = sum(row["ran"] for row in rows)
            # Reuse the native command constructor while holding BuildLock throughout.
            # Do not nest run_locked_lake_build (which would acquire the same lock).
            run("native-route-build", lake_build_command([TARGET]))
            from tools.route_certificate import certificate_from_route, emit_lean
            for i, route in enumerate(FIXTURES):
                namespace = "namespace.end" if i == 7 else f"RouteFixture{i}"
                path = out / f"RouteFixture{i}.lean"
                path.write_text(emit_lean(certificate_from_route(route), namespace))
                _, verdict = run(f"RouteFixture{i}", ["lake", "env", "lean", str(path.relative_to(root))])
                audit(verdict, namespace)

            forged = emit_lean(certificate_from_route([0, 0, 1, 1]), "ForgedRoute")
            original = "def depth : Fin 4 → ℕ := ![0, 1, 2, 2]"
            require(forged.count(original) == 1, "Emitter depth layout changed")
            forged = forged.replace(original, "def depth : Fin 4 → ℕ := ![0, 0, 0, 0]")
            lines = forged.splitlines()
            start = next(i + 1 for i, s in enumerate(lines) if s.startswith("theorem local_certificate"))
            end = next(i + 1 for i, s in enumerate(lines) if s.startswith("theorem certified_inverse"))
            path = out / "ForgedRoute.lean"
            path.write_text(forged)
            code, verdict = run("forged-rejection", ["lake", "env", "lean", str(path.relative_to(root))],
                                success=False)
            errors = [int(n) for n in re.findall(r"ForgedRoute\.lean:(\d+):\d+: error:", verdict)]
            require(code != 0 and any(start <= line < end for line in errors),
                    "Forged depth was not rejected within the local_certificate proof")
            require(snapshot() == before, "Source changed during acceptance")
            status.update(result="success", generated_certificates=8, theorem_audits=24,
                          forged_depth_rejected_at="local_certificate", source_hashes_stable=True)
    except BaseException as exc:
        status["error"] = str(exc)
        raise
    finally:
        (out / "status.json").write_text(json.dumps(status, indent=2) + "\n")


if __name__ == "__main__":
    main()
