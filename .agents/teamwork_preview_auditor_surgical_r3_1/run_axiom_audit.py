#!/usr/bin/env python3
import os
import sys
from pathlib import Path

# Add repo root to sys.path
repo_root = Path("/home/goutev/info-geometry-lean")
if str(repo_root) not in sys.path:
    sys.path.insert(0, str(repo_root))

import subprocess
import time
from tools.build_lock import acquire_build_lock

cand_path = repo_root / ".agents/sandbox_surgical_o1/lean/InfoGeometry/Canonical/Hartwig1976SVDMoorePenroseBorder.lean"
audit_dir = repo_root / ".agents/teamwork_preview_auditor_surgical_r3_1"
test_file = audit_dir / "test_axioms.lean"

cand_text = cand_path.read_text(encoding="utf-8")

# Extract namespace ending or append commands inside namespace
theorems_to_check = [
    "baseA_isMoorePenrose",
    "case1Z_eq",
    "case1Border_isMoorePenrose",
    "case1Schur_isMoorePenrose",
    "case3Border_isMoorePenrose",
    "case3Schur_isMoorePenrose",
    "borderPermutation_sq_eq_one",
    "borderPermutation_star_eq_self",
    "unitConj_isMoorePenrose",
    "case1_conjugated_border_isMoorePenrose",
]

axiom_commands = "\n".join([f"#print axioms {thm}" for thm in theorems_to_check])

# Place axiom commands before 'end InfoGeometry.Canonical.Hartwig1976SVDMoorePenroseBorder'
ns_end = "end InfoGeometry.Canonical.Hartwig1976SVDMoorePenroseBorder"
if ns_end in cand_text:
    modified_code = cand_text.replace(ns_end, f"\n{axiom_commands}\n\n{ns_end}")
else:
    modified_code = cand_text + f"\n\n{axiom_commands}\n"

test_file.write_text(modified_code, encoding="utf-8")
print(f"Generated {test_file} with {len(theorems_to_check)} #print axioms commands.")

print("Acquiring build lock...")
t0 = time.time()
with acquire_build_lock(None, "auditor_surgical_r3_1:axiom_audit", block=True):
    lock_wait = time.time() - t0
    print(f"Build lock acquired after {lock_wait:.2f}s. Running `lake env lean`...")
    t1 = time.time()
    res = subprocess.run(
        ["lake", "env", "lean", str(test_file)],
        capture_output=True,
        text=True
    )
    lean_time = time.time() - t1
    print(f"`lake env lean` finished in {lean_time:.2f}s with returncode {res.returncode}")

print("\n--- STDOUT ---")
print(res.stdout)
if res.stderr:
    print("\n--- STDERR ---")
    print(res.stderr)

if res.returncode != 0:
    print(f"FAILED: lean exited with code {res.returncode}", file=sys.stderr)
    sys.exit(res.returncode)

# Parse stdout for axioms
lines = res.stdout.splitlines()
results = {}
current_thm = None
for line in lines:
    for thm in theorems_to_check:
        if line.startswith(f"'{thm}'") or f"'{thm}' depends on axioms:" in line:
            current_thm = thm
            results[thm] = []
            break
    if current_thm and ("[" in line or line.strip().startswith("propext") or line.strip().startswith("Classical") or line.strip().startswith("Quot") or line.strip().startswith("Lean.") or line.strip().startswith("sorryAx")):
        tokens = line.replace("[", "").replace("]", "").replace(",", "").split()
        for tok in tokens:
            if tok not in results[current_thm]:
                results[current_thm].append(tok)

print("\n=== AXIOM ANALYSIS REPORT ===")
prohibited_found = False
allowed_axioms = {"propext", "Classical.choice", "Quot.sound"}

for thm in theorems_to_check:
    raw_axioms = results.get(thm, [])
    print(f"Theorem: {thm}")
    print(f"  Axioms: {raw_axioms}")
    for ax in raw_axioms:
        if "ofReduceBool" in ax or "sorryAx" in ax:
            print(f"  [PROHIBITED AXIOM DETECTED]: {ax}")
            prohibited_found = True
        elif ax not in allowed_axioms:
            print(f"  [UNEXPECTED AXIOM]: {ax}")
            prohibited_found = True

if prohibited_found:
    print("\nVERDICT: INTEGRITY VIOLATION - Prohibited axioms present!")
    sys.exit(1)
else:
    print("\nVERDICT: CLEAN - Strictly 0 ofReduceBool, 0 sorryAx, only foundational axioms used.")
