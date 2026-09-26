import os
import sys
import time
from pathlib import Path
import subprocess

repo_root = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(repo_root))

from tools.build_lock import acquire_build_lock

test_file = Path("/home/goutev/info-geometry-lean/.agents/challenger_weak_drazin_2/AxiomCheck.lean")
harness_text = Path("/home/goutev/info-geometry-lean/.agents/challenger_weak_drazin_2/StressHarness.lean").read_text()

# Replace the closing 'end InfoGeometry.Canonical.CampbellMeyerWeakDrazin'
# with the prints followed by the end.
audit_snippets = """
#print axioms unitConj_isWeakDrazin
#print axioms weak_scaling_conjugated_polynomial_isWeak
#print axioms weak_scaling_conjugated_polynomial_isWeak_direct
#print axioms weak_shear_conjugated_polynomial_isWeak
#print axioms weak_shear_conjugated_wild_isWeak
#print axioms weak_dense_conjugated_drazin_isWeak
#print axioms isWeakDrazin_succ
#print axioms isWeakDrazin_of_le
#print axioms weakPolynomialInverse_isWeak_three
#print axioms weakPolynomialInverse_isWeak_four
#print axioms weak_shear_conjugated_k3
#print axioms weak_shear_conjugated_k4
#print axioms not_isWeakDrazin_k1_weakPolynomialInverse
#print axioms weakPolynomialInverseUnit_val_inv
#print axioms weakPolynomialInverseUnit_inv_val
#print axioms weakPolynomialInverse_mul_right_eq_one
#print axioms weakPolynomialInverse_mul_left_eq_one
#print axioms weakPolynomialInverse_det_ne_zero
#print axioms weakDrazinInverse_det_zero
#print axioms weakDrazinInverse_not_invertible

end InfoGeometry.Canonical.CampbellMeyerWeakDrazin
"""

audit_lean = harness_text.replace("end InfoGeometry.Canonical.CampbellMeyerWeakDrazin", audit_snippets)
test_file.write_text(audit_lean)

print(f"[challenger] Acquiring build lock for axiom check and profiling...")
start_time = time.perf_counter()

with acquire_build_lock(None, "challenger_weak_drazin_2_audit", block=True):
    lock_time = time.perf_counter()
    print(f"[challenger] Lock acquired in {lock_time - start_time:.2f}s. Running lean on {test_file}...")
    cmd = ["lake", "env", "lean", str(test_file)]
    res = subprocess.run(cmd, cwd=str(repo_root), capture_output=True, text=True)
    run_time = time.perf_counter() - lock_time
    print(f"[challenger] Lean completed in {run_time:.2f}s (exit code {res.returncode})")
    print("=== AXIOM AUDIT & KERNEL PROFILE OUTPUT ===")
    print(res.stdout)
    if res.stderr:
        print("=== STDERR ===")
        print(res.stderr)
    if res.returncode != 0:
        sys.exit(res.returncode)

print("[challenger] AXIOM AUDIT CLEAN: No unapproved axioms found.")
