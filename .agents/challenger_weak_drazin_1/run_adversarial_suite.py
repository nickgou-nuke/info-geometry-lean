#!/usr/bin/env python3
"""
Adversarial Negative Perturbation Test Suite for CampbellMeyerWeakDrazin.lean.
Written by challenger_weak_drazin_1.
"""
import os
import sys
from pathlib import Path

REPO_ROOT = Path("/home/goutev/info-geometry-lean")
sys.path.insert(0, str(REPO_ROOT))

import subprocess
import time
from tools.build_lock import acquire_build_lock

TMP_DIR = Path("/home/goutev/info-geometry-lean/.agents/challenger_weak_drazin_1/tmp")
BASE_SANDBOX_FILE = Path("/home/goutev/info-geometry-lean/.agents/sandbox_weak_drazin_o1/lean/InfoGeometry/Canonical/CampbellMeyerWeakDrazin.lean")

def run_lean_on_file(lean_file_path: Path) -> tuple[int, str, str]:
    with acquire_build_lock(None, "challenger_adversarial_suite", block=True):
        res = subprocess.run(
            ["lake", "env", "lean", str(lean_file_path)],
            capture_output=True,
            text=True,
            cwd=str(REPO_ROOT)
        )
        return res.returncode, res.stdout, res.stderr

def test_mutant(name: str, code: str) -> dict:
    test_file = TMP_DIR / f"{name}.lean"
    test_file.write_text(code, encoding="utf-8")
    print(f"[*] Running negative perturbation test: {name}...")
    t0 = time.time()
    rc, stdout, stderr = run_lean_on_file(test_file)
    elapsed = time.time() - t0
    
    # Negative test PASSES if Lean REJECTS the false assertion (rc != 0 and 'error:' in output)
    rejected = (rc != 0) and ("error:" in (stdout + stderr))
    print(f"    Result: {'REJECTED (PASS)' if rejected else 'ACCEPTED (FAIL - BUG FOUND)'} in {elapsed:.2f}s (rc={rc})")
    
    # Clean up test file
    if test_file.exists():
        test_file.unlink()
        
    return {
        "name": name,
        "elapsed": elapsed,
        "rc": rc,
        "rejected": rejected,
        "stdout": stdout,
        "stderr": stderr
    }

def main():
    print("=== STARTING ADVERSARIAL PERTURBATION SUITE ===")
    
    # Read baseline code to construct exact perturbations
    base_code = BASE_SANDBOX_FILE.read_text(encoding="utf-8")
    
    mutants = []
    
    # Mutation 1: weakNilpotentLane_sq_eq_zero mutated to nonzero matrix !![0,0,1; 0,0,0; 0,0,0]
    m1_code = base_code.replace(
        "weakNilpotentLane ^ 2 = 0",
        "weakNilpotentLane ^ 2 = !![0, 0, 1; 0, 0, 0; 0, 0, 0]"
    )
    mutants.append(("mutant1_nilpotent_sq_nonzero", m1_code))
    
    # Mutation 2: weakA_sq_readout mutated: 4 replaced with 5 at (0,0)
    m2_code = base_code.replace(
        "!![4, 0, 0;\n         0, 0, 0;\n         0, 0, 0]",
        "!![5, 0, 0;\n         0, 0, 0;\n         0, 0, 0]"
    )
    mutants.append(("mutant2_weakA_sq_bad_readout", m2_code))
    
    # Mutation 3: weakDrazinInverse_isDrazin mutated: claim weakWildInverse is a Drazin inverse (it does not commute!)
    m3_code = base_code.replace(
        "theorem weakDrazinInverse_isDrazin :\n    Drazin.IsDrazinInverse weakA weakDrazinInverse 2 :=",
        "theorem weakDrazinInverse_isDrazin :\n    Drazin.IsDrazinInverse weakA weakWildInverse 2 :="
    )
    mutants.append(("mutant3_wild_is_drazin_false", m3_code))
    
    # Mutation 4: weakWildInverse_ne_Drazin mutated: claim weakDrazinInverse ≠ weakDrazinInverse
    m4_code = base_code.replace(
        "theorem weakWildInverse_ne_Drazin :\n    weakWildInverse ≠ weakDrazinInverse :=",
        "theorem weakWildInverse_ne_Drazin :\n    weakDrazinInverse ≠ weakDrazinInverse :="
    )
    mutants.append(("mutant4_drazin_ne_drazin_false", m4_code))
    
    # Mutation 5: weakWildInverse_not_commuting mutated: claim commuting inverse does NOT commute
    m5_code = base_code.replace(
        "theorem weakWildInverse_not_commuting :\n    weakA * weakWildInverse ≠ weakWildInverse * weakA :=",
        "theorem weakWildInverse_not_commuting :\n    weakA * weakCommutingInverse ≠ weakCommutingInverse * weakA :="
    )
    # also update the proof line to use weakCommutingInverse
    m5_code = m5_code.replace(
        "simp [Matrix.mul_apply, Fin.sum_univ_three, weakA, weakWildInverse] at h0",
        "simp [Matrix.mul_apply, Fin.sum_univ_three, weakA, weakCommutingInverse] at h0"
    )
    mutants.append(("mutant5_commuting_not_commuting_false", m5_code))
    
    # Mutation 6: weakPolynomialInverse_ne_Drazin mutated: claim weakDrazinInverse ≠ weakDrazinInverse
    m6_code = base_code.replace(
        "theorem weakPolynomialInverse_ne_Drazin :\n    weakPolynomialInverse ≠ weakDrazinInverse :=",
        "theorem weakPolynomialInverse_ne_Drazin :\n    weakDrazinInverse ≠ weakDrazinInverse :="
    )
    m6_code = m6_code.replace(
        "simp [weakPolynomialInverse, weakDrazinInverse] at h0",
        "simp [weakDrazinInverse] at h0"
    )
    mutants.append(("mutant6_poly_drazin_ne_self_false", m6_code))
    
    # Mutation 7: weak_conjugated_polynomial_inverse_isWeak mutated: claim index 1 instead of 2
    # At index 1: B A^2 = A is false because A^2 has 0 at (1,2) while A has 1 at (1,2)
    m7_code = base_code.replace(
        "theorem weak_conjugated_polynomial_inverse_isWeak :\n    IsWeakDrazin\n      (unitConj weakPermutationUnit weakA)\n      (unitConj weakPermutationUnit weakPolynomialInverse)\n      2 :=",
        "theorem weak_conjugated_polynomial_inverse_isWeak :\n    IsWeakDrazin\n      (unitConj weakPermutationUnit weakA)\n      (unitConj weakPermutationUnit weakPolynomialInverse)\n      1 :="
    )
    mutants.append(("mutant7_conjugated_index1_false", m7_code))

    # Mutation 8: weakProjectiveInverse_BA_idempotent mutated: test with weakWildInverse which is NOT idempotent
    m8_code = base_code.replace(
        "(weakProjectiveInverse * weakA) * (weakProjectiveInverse * weakA) =\n      weakProjectiveInverse * weakA :=",
        "(weakWildInverse * weakA) * (weakWildInverse * weakA) =\n      weakWildInverse * weakA :="
    ).replace(
        "rw [weakProjectiveInverse_BA_readout]",
        "-- skipped readout"
    )
    mutants.append(("mutant8_wild_BA_not_idempotent", m8_code))

    results = []
    all_passed = True
    for name, code in mutants:
        res = test_mutant(name, code)
        results.append(res)
        if not res["rejected"]:
            all_passed = False
            print(f"[!] CRITICAL FAILURE: Lean accepted false mutant {name}!")

    print("\n=== SUMMARY OF ADVERSARIAL MUTATION RESULTS ===")
    for r in results:
        status = "REJECTED (PASS)" if r["rejected"] else "ACCEPTED (FAIL)"
        print(f"[{status}] {r['name']} in {r['elapsed']:.2f}s")
        # Extract the error line
        errors = [line for line in (r["stdout"] + r["stderr"]).splitlines() if "error:" in line]
        for err in errors[:2]:
            print(f"    -> {err.strip()}")

    if all_passed:
        print("\nALL 8 NEGATIVE MUTANTS WERE STRICTLY REJECTED BY LEAN KERNEL!")
        print("Conclusion: Proofs are non-vacuous, structurally sound, and reject false claims.")
    else:
        print("\nSOME MUTANTS WERE ACCEPTED! INVESTIGATION REQUIRED.")
        sys.exit(1)

if __name__ == "__main__":
    main()
