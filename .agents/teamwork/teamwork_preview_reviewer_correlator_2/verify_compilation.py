#!/usr/bin/env python3
import sys
import os
import subprocess
import time

sys.path.insert(0, os.path.abspath("."))
from tools.build_lock import acquire_build_lock

sandbox_file = ".agents/sandbox_correlator/lean/InfoGeometry/Detector/FieldCorrelatorProjection.lean"
print(f"[{time.strftime('%X')}] Requesting build lock for reviewer_2 compilation check...")

t0 = time.time()
with acquire_build_lock(None, "reviewer_correlator_2", block=True):
    t_acq = time.time()
    print(f"[{time.strftime('%X')}] Lock acquired after {t_acq - t0:.2f}s. Running lake env lean on {sandbox_file}...")
    res = subprocess.run(
        ["lake", "env", "lean", "--threads", "1", sandbox_file],
        capture_output=True,
        text=True
    )
    t_end = time.time()
    print(f"[{time.strftime('%X')}] Lean invocation completed in {t_end - t_acq:.2f}s.")

print("Return code:", res.returncode)
print("STDOUT:\n", res.stdout)
print("STDERR:\n", res.stderr)
assert res.returncode == 0, f"Lean typechecking failed with returncode {res.returncode}"
print("VERIFICATION RESULT: SUCCESS (return code 0, clean compilation)")
