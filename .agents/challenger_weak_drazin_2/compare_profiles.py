import os
import sys
import time
from pathlib import Path
import subprocess

repo_root = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(repo_root))

from tools.build_lock import acquire_build_lock

live_file = repo_root / "lean" / "InfoGeometry" / "Canonical" / "CampbellMeyerWeakDrazin.lean"
sandbox_file = repo_root / ".agents" / "sandbox_weak_drazin_o1" / "lean" / "InfoGeometry" / "Canonical" / "CampbellMeyerWeakDrazin.lean"

print(f"[profiler] Acquiring build lock for comparative profiling...")

with acquire_build_lock(None, "challenger_weak_drazin_2_profile_compare", block=True):
    # Benchmark Sandbox File
    t0 = time.perf_counter()
    res_sandbox = subprocess.run(
        ["lake", "env", "lean", "--profile", str(sandbox_file)],
        cwd=str(repo_root),
        capture_output=True,
        text=True,
    )
    t_sandbox = time.perf_counter() - t0
    
    # Benchmark Live File
    t0 = time.perf_counter()
    res_live = subprocess.run(
        ["lake", "env", "lean", "--profile", str(live_file)],
        cwd=str(repo_root),
        capture_output=True,
        text=True,
    )
    t_live = time.perf_counter() - t0

print("\n=== PROFILE COMPARISON SUMMARY ===")
print(f"Sandbox file ({sandbox_file.name}): {t_sandbox:.2f}s (exit {res_sandbox.returncode})")
print(f"Live file ({live_file.name}): {t_live:.2f}s (exit {res_live.returncode})")

print("\n=== SANDBOX LEAN PROFILE TOP OUTPUT ===")
for line in res_sandbox.stdout.splitlines()[:30]:
    print(line)

print("\n=== LIVE LEAN PROFILE TOP OUTPUT ===")
for line in res_live.stdout.splitlines()[:30]:
    print(line)
