#!/usr/bin/env python3
import os
import sys
import subprocess
import time
from pathlib import Path

sys.path.insert(0, os.path.abspath("."))
from tools.build_lock import acquire_build_lock

sandbox_file = ".agents/sandbox_connes_hodge/lean/DAG/ConnesHodgeBridge.lean"

print("=== Acquiring Build Lock for Forensic Compilation Verification ===")
with acquire_build_lock(None, "auditor_chb", block=True):
    print("Lock acquired successfully!")
    
    # 1. Direct compilation of sandbox file with profiling
    print("\n--- 1. Direct Compilation of Sandbox File ---")
    t0 = time.time()
    res1 = subprocess.run(
        ["lake", "env", "lean", "--profile", "--threads", "1", sandbox_file],
        capture_output=True,
        text=True
    )
    t1 = time.time()
    print(f"Compilation finished in {t1 - t0:.3f} s, returncode: {res1.returncode}")
    print("STDOUT:")
    print(res1.stdout)
    filtered_stderr = [l for l in res1.stderr.splitlines() if "manifest out of date" not in l]
    print("STDERR (filtered):")
    for l in filtered_stderr:
        print(" ", l)
    assert res1.returncode == 0, f"Compilation failed with returncode {res1.returncode}"

    # 2. Axiom inspection of all declarations
    print("\n--- 2. Axiom Inspection (#print axioms) ---")
    decls = [
        "DAG.ConnesHodgeBridge.ConnesCorrespondence",
        "DAG.ConnesHodgeBridge.fromTwoComplex",
        "DAG.ConnesHodgeBridge.fromHodgeData",
        "DAG.ConnesHodgeBridge.fromTwoComplex_edgeCount",
        "DAG.ConnesHodgeBridge.fromTwoComplex_harmonicDim",
        "DAG.ConnesHodgeBridge.fromTwoComplex_cocycleDimUpperBound",
        "DAG.ConnesHodgeBridge.fromTwoComplex_eulerChar",
        "DAG.ConnesHodgeBridge.fromHodgeData_edgeCount",
        "DAG.ConnesHodgeBridge.fromHodgeData_harmonicDim",
        "DAG.ConnesHodgeBridge.fromHodgeData_cocycleDimUpperBound",
        "DAG.ConnesHodgeBridge.fromHodgeData_eulerChar",
        "DAG.ConnesHodgeBridge.fromTwoComplex_harmonicDim_eq_cocycleDimUpperBound",
        "DAG.ConnesHodgeBridge.fromHodgeData_harmonicDim_eq_cocycleDimUpperBound",
        "DAG.ConnesHodgeBridge.harmonicDim_eq_cocycleDimUpperBound_fromTwoComplex",
        "DAG.ConnesHodgeBridge.harmonicDim_eq_cocycleDimUpperBound_fromHodgeData",
        "DAG.ConnesHodgeBridge.fromHodgeData_fromTwoComplex_edgeCount",
        "DAG.ConnesHodgeBridge.fromHodgeData_fromTwoComplex_eulerChar"
    ]
    with open(sandbox_file) as f:
        code = f.read()
    axiom_checks = "\n".join([f"#print axioms {d}" for d in decls])
    res2 = subprocess.run(
        ["lake", "env", "lean", "--stdin"],
        input=code + "\n\n" + axiom_checks + "\n",
        capture_output=True,
        text=True
    )
    print("Axiom query returncode:", res2.returncode)
    print("Axiom query output:")
    for l in res2.stdout.splitlines():
        print(" ", l)
    assert res2.returncode == 0, "Axiom query failed"
    assert "sorryAx" not in res2.stdout, "sorryAx detected in declarations!"

    # 3. End-to-end sandbox verification script
    print("\n--- 3. Running .agents/sandbox_connes_hodge/scripts/verify_sandbox.sh ---")
    res3 = subprocess.run(
        ["bash", ".agents/sandbox_connes_hodge/scripts/verify_sandbox.sh"],
        capture_output=True,
        text=True
    )
    print("Script returncode:", res3.returncode)
    print("STDOUT:\n", res3.stdout)
    filtered_stderr3 = [l for l in res3.stderr.splitlines() if "manifest out of date" not in l]
    if filtered_stderr3:
        print("STDERR (filtered):\n", "\n".join(filtered_stderr3))
    assert res3.returncode == 0, "verify_sandbox.sh failed"
    assert "=== All Sandbox Verifications PASSED ===" in res3.stdout

print("\n=== All Forensic Compilation Checks PASSED ===")
