import os
import sys
import time
from pathlib import Path

repo_root = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(repo_root))

from tools.build_lock import acquire_build_lock
import subprocess

target = ".agents/challenger_weak_drazin_2/StressHarness.lean"
print(f"[challenger] Acquiring build lock for {target}...")
start_time = time.perf_counter()

with acquire_build_lock(None, "challenger_weak_drazin_2_harness", block=True):
    lock_time = time.perf_counter()
    print(f"[challenger] Lock acquired in {lock_time - start_time:.2f}s. Running lake env lean...")
    cmd = ["lake", "env", "lean", target]
    res = subprocess.run(cmd, cwd=str(repo_root), capture_output=True, text=True)
    compile_time = time.perf_counter() - lock_time
    print(f"[challenger] Lean process exited in {compile_time:.2f}s with code {res.returncode}")
    print("--- STDOUT ---")
    print(res.stdout)
    print("--- STDERR ---")
    print(res.stderr)
    if res.returncode != 0:
        sys.exit(res.returncode)

print(f"[challenger] SUCCESS: All stress-test theorems kernel-verified!")
