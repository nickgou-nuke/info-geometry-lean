#!/usr/bin/env python3
"""Build and audit GRH compatibility under the repository's shared build lock."""

from __future__ import annotations

import argparse
import json
import os
from pathlib import Path
import re
import subprocess
import sys
from datetime import datetime, timezone

from audit_axioms import AuditFailure, validate_output
from verify_sources import PACKAGE, ROOT, TOOLCHAINS, NATIVE_TARGETS, SourceFailure, lane_directory, verify

sys.path.insert(0, str(ROOT))
from tools.build_lock import BuildLock, DEFAULT_BUILD_LOCK_PATH  # noqa: E402


def write_json(path: Path, value: object) -> None:
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def run(command: list[str], directory: Path, log: Path, env: dict[str, str], lock: BuildLock) -> tuple[int, str]:
    print(f"[grh:{directory.name}] {' '.join(command)}", flush=True)
    with log.open("w", encoding="utf-8") as output:
        process = subprocess.Popen(command, cwd=directory, env=env, text=True,
                                   stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                                   encoding="utf-8", errors="replace",
                                   pass_fds=(lock.fileno(),), start_new_session=True)
        try:
            assert process.stdout is not None
            for line in process.stdout:
                print(line, end="", flush=True)
                output.write(line)
                output.flush()
            code = process.wait()
        except BaseException:
            # A logging/UI interruption does not authorize terminating Lake.
            # Drain its pipe and retain the shared lock until it finishes.
            if process.poll() is None:
                if process.stdout is not None:
                    for _ in process.stdout:
                        pass
                process.wait()
            raise
    return code, log.read_text(encoding="utf-8")


def check_lane(lane: str, lake: str, cache: bool, env: dict[str, str], lock: BuildLock) -> None:
    directory = lane_directory(lane)
    evidence = PACKAGE / "artifacts" / lane
    evidence.mkdir(parents=True, exist_ok=True)
    report = {"status": "RUNNING", "lane": lane,
              "started_utc": datetime.now(timezone.utc).isoformat(), "commands": []}
    write_json(evidence / "validation.json", report)

    def command(args: list[str], name: str, *, audit: bool = False) -> tuple[int, str]:
        code, text = run([lake, *args], directory, evidence / f"{name}.log", env, lock)
        report["commands"].append({"command": [lake, *args], "cwd": str(directory), "exit_code": code})
        write_json(evidence / "validation.json", report)
        if code and not audit:
            raise SourceFailure(f"{lane} {name} failed with exit code {code}; see {evidence / (name + '.log')}")
        return code, text

    try:
        before = verify(lane)
        write_json(evidence / "sources-before.json", before)
        _, version = command(["env", "lean", "--version"], "lean-version")
        expected = TOOLCHAINS[lane].split(":v")[1]
        if re.search(rf"\bversion {re.escape(expected)}(?:,|\s|\))", version) is None:
            raise SourceFailure(f"Actual Lean executable does not match {TOOLCHAINS[lane]}")
        verify(lane, checkouts=True)
        if cache:
            roots = before["mathlib_cache_roots"] if lane == "native" else []
            command(["exe", "cache", "get", *roots], "mathlib-cache")
            verify(lane, checkouts=True)
        if lane == "external":
            # Distinguish a failure in the pinned readable proof from a failure
            # in our adapters. The complete declaration audit still follows.
            command(["--rehash", "build", "GRH/+New.Main"], "upstream-build")
            upstream_sources = verify(lane, checkouts=True)
            write_json(evidence / "sources-upstream.json", upstream_sources)
            if before["source_sha256"] != upstream_sources["source_sha256"]:
                raise SourceFailure("Source/configuration changed during the upstream build")
            report["upstream_build"] = {"status": "PASS", "target": "GRH/+New.Main"}
            write_json(evidence / "validation.json", report)
        targets = list(NATIVE_TARGETS) if lane == "native" else ["InfoGeometryGRH"]
        command(["--rehash", "build", *targets], "build")
        audit_file = "NativeAxiomAudit.lean" if lane == "native" else "InfoGeometryGRH/AxiomAudit.lean"
        # Direct Lean invocations do not inherit Lake's per-module resource
        # options. Match the package bounds for the fresh declaration walk.
        code, output = command(["env", "lean", "--tstack=400000", "-DmaxHeartbeats=4000000",
                                audit_file], "axioms", audit=True)
        try:
            audit_result = validate_output(output, lean_exit_code=code,
                                           scope="native" if lane == "native" else "integration")
        except AuditFailure as exc:
            write_json(evidence / "axiom-result.json", {"status": "FAIL", "reason": str(exc)})
            raise
        write_json(evidence / "axiom-result.json", audit_result)
        after = verify(lane, checkouts=True)
        write_json(evidence / "sources-after.json", after)
        if before["source_sha256"] != after["source_sha256"]:
            raise SourceFailure("Source/configuration changed during validation; rerun on a stable tree")
        report["status"] = "PASS"
        report["toolchain"] = TOOLCHAINS[lane]
        report["audit"] = audit_result
    except BaseException as exc:
        report["status"] = "FAIL"
        report["reason"] = str(exc)
        raise
    finally:
        report["finished_utc"] = datetime.now(timezone.utc).isoformat()
        write_json(evidence / "validation.json", report)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lane", choices=("native", "external", "all"), default="all")
    parser.add_argument("--cache", action="store_true", help="Fetch the pinned Mathlib build artifacts before compiling")
    parser.add_argument("--native-lake", default=os.environ.get("GRH_NATIVE_LAKE", "lake"))
    parser.add_argument("--external-lake", default=os.environ.get("GRH_EXTERNAL_LAKE", "lake"))
    parser.add_argument("--threads", type=int, default=2)
    args = parser.parse_args()
    if args.threads < 1:
        parser.error("--threads must be positive")
    env = os.environ.copy()
    env["LEAN_NUM_THREADS"] = str(args.threads)
    # Lake must establish import paths for the selected package itself.
    for name in ("LEAN_PATH", "LEAN_SRC_PATH"):
        if env.get(name):
            parser.error(f"Unset {name} before validating an isolated package")
    lanes = ("native", "external") if args.lane == "all" else (args.lane,)
    try:
        for lane in lanes:
            verify(lane)
        print(f"Waiting for shared build lock: {DEFAULT_BUILD_LOCK_PATH}", flush=True)
        with BuildLock(DEFAULT_BUILD_LOCK_PATH, f"grh-compatibility:{os.getpid()}", block=True) as lock:
            for lane in lanes:
                check_lane(lane, args.native_lake if lane == "native" else args.external_lake,
                           args.cache, env, lock)
        print("GRH compatibility build and fresh axiom audit passed: " + ", ".join(lanes))
        return 0
    except (OSError, ValueError, KeyError, StopIteration) as exc:
        print(f"GRH compatibility failed: {exc}", file=sys.stderr)
        return 1
    except KeyboardInterrupt:
        return 130


if __name__ == "__main__":
    raise SystemExit(main())
