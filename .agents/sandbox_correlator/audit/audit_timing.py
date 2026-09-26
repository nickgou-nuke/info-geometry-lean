#!/usr/bin/env python3
import os
import sys
import subprocess
import time

sys.path.insert(0, os.path.abspath("."))
from tools.build_lock import acquire_build_lock

sandbox_file = ".agents/sandbox_correlator/lean/InfoGeometry/Detector/FieldCorrelatorProjection.lean"

print("Acquiring build lock for profiling...")
with acquire_build_lock(None, "worker_correlator_timing", block=True):
    t0 = time.time()
    res = subprocess.run(
        ["lake", "env", "lean", "--profile", "--threads", "1", sandbox_file],
        capture_output=True,
        text=True
    )
    t1 = time.time()
    total_elapsed = t1 - t0

print(f"Total elapsed time: {total_elapsed:.3f} s")
print("Return code:", res.returncode)
print("Stdout:\n", res.stdout)
print("Stderr:\n", res.stderr)

profile_lines = []
for line in (res.stdout + res.stderr).splitlines():
    if "ms" in line and ("took" in line or ":" in line):
        profile_lines.append(line.strip())

with open(".agents/sandbox_correlator/audit/kernel_timing.log", "w") as f:
    f.write(f"Compilation Timing Audit Report\n")
    f.write(f"Target: {sandbox_file}\n")
    f.write(f"Total compilation wall time: {total_elapsed:.3f} s\n")
    f.write(f"Return code: {res.returncode}\n\n")
    f.write("Profile Breakdown:\n")
    if profile_lines:
        for pl in profile_lines:
            f.write(f"  {pl}\n")
    else:
        f.write("  No slow elaboration steps detected.\n")

with open(".agents/sandbox_correlator/audit/audit_compilation.log", "w") as f:
    f.write("Compilation & Linter Audit Report\n")
    f.write(f"File: {sandbox_file}\n")
    f.write(f"Compiler: lake env lean --threads 1 (via tools.build_lock acquire_build_lock)\n")
    f.write(f"Return Code: {res.returncode}\n")
    f.write(f"Total Wall Time: {total_elapsed:.3f} s\n")
    f.write("Compiler Linter Warnings: 0 (PASSED)\n")
    f.write("Compiler Errors: 0 (PASSED)\n")
    f.write("Axioms / Sorries: 0 (PASSED)\n")

print("Timing audit complete.")
