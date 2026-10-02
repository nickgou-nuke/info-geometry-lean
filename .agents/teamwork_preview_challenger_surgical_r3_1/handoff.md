# Empirical Challenger Handoff Report

## Verdict: APPROVE

Candidate File Under Audit:
`/home/goutev/info-geometry-lean/.agents/sandbox_surgical_o1/lean/InfoGeometry/Canonical/Hartwig1976SVDMoorePenroseBorder.lean`

---

### 1. Observation

Direct empirical testing was performed using the locked Lean single-file runner via `tools.build_lock` and Lake environment.

1. **Baseline Compilation**:
   - Command:
     ```bash
     python3 -c "
     import sys, subprocess
     from tools.build_lock import acquire_build_lock
     target_file = sys.argv[1]
     with acquire_build_lock(None, f'challenger-check:{target_file}', block=True):
         res = subprocess.run(['lake', 'env', 'lean', target_file])
         sys.exit(res.returncode)
     " "/home/goutev/info-geometry-lean/.agents/sandbox_surgical_o1/lean/InfoGeometry/Canonical/Hartwig1976SVDMoorePenroseBorder.lean"
     ```
   - Result: Exit code `0`. Clean compilation with 0 errors and 0 warnings (excluding upstream manifest warnings).
   - grep check for `sorry`, `admit`, `native_decide`, `decide`: 0 occurrences found across all 336 lines.

2. **Axiom Soundness Audit (`scratch/test_axioms.lean`)**:
   - Output from Lean kernel `#print axioms`:
     - `'baseA_isMoorePenrose' depends on axioms: [propext, Classical.choice, Quot.sound]`
     - `'case1Border_isMoorePenrose' depends on axioms: [propext, Classical.choice, Quot.sound]`
     - `'case1Schur_isMoorePenrose' depends on axioms: [propext, Classical.choice, Quot.sound]`
     - `'case3Border_isMoorePenrose' depends on axioms: [propext, Classical.choice, Quot.sound]`
     - `'case3Schur_isMoorePenrose' depends on axioms: [propext, Classical.choice, Quot.sound]`
     - `'unitConj_isMoorePenrose' depends on axioms: [propext, Classical.choice, Quot.sound]`
     - `'case1_conjugated_border_isMoorePenrose' depends on axioms: [propext, Classical.choice, Quot.sound]`
   - No custom axioms, sorryAx, or unverified constants are present.

3. **Negative Perturbation 1: Corrupted `case1Border` entry (`scratch/perturbation_test1_fail.lean`)**:
   - Modification: Entry `(2,2)` changed from `5` to `999`.
   - Command: `lake env lean scratch/perturbation_test1_fail.lean`
   - Result: Exit code `1`.
   - Verbatim Compiler Error:
     ```
     /home/goutev/info-geometry-lean/scratch/perturbation_test1_fail.lean:21:72: error: unsolved goals
     case a.«_@»._internal._hyg.0.«2».«0»
     ⊢ False

     case a.«_@»._internal._hyg.0.«2».«2»
     ⊢ False
     ```

4. **Negative Perturbation 2: Corrupted `case1Schur` entry (`scratch/perturbation_test2_fail.lean`)**:
   - Modification: Entry `(0,0)` of Schur complement changed from `7/5` to `999`.
   - Command: `lake env lean scratch/perturbation_test2_fail.lean`
   - Result: Exit code `1`.
   - Verbatim Compiler Error:
     ```
     /home/goutev/info-geometry-lean/scratch/perturbation_test2_fail.lean:19:55: error: unsolved goals
     case a.«_@»._internal._hyg.0.«0».«0»
     ⊢ 999 * (5 / 7) = 1
     ```

5. **Negative Perturbation 3: Corrupted `case3BorderMP` candidate violating MP1 (`scratch/perturbation_test3_fail.lean`)**:
   - Modification: Entry `(1,1)` of `case3BorderMP` changed from `-5` to `999`.
   - Adversarial claim: `case3Border * case3BorderMP_bad * case3Border = case3Border`
   - Command: `lake env lean scratch/perturbation_test3_fail.lean`
   - Result: Exit code `1`.
   - Verbatim Compiler Error:
     ```
     /home/goutev/info-geometry-lean/scratch/perturbation_test3_fail.lean:21:67: error: unsolved goals
     case a.«_@»._internal._hyg.0.«2».«2»
     ⊢ False
     ```

6. **Formal Adversarial Oracle Refutations (`scratch/test_hartwig_adversarial_oracle.lean`)**:
   - Formally proved the negations in Lean:
     - `case1Border_pert_violates_target : case1Border_pert * case1BorderMP ≠ !![1, 0, 0; 0, 0, 0; 0, 0, 1]`
     - `case1Schur_pert_violates_target : case1Schur_pert * case1SchurMP ≠ !![1, 0; 0, 0]`
     - `case3Border_bad_violates_mp1 : case3Border * case3BorderMP_bad * case3Border ≠ case3Border`
   - Result: Exit code `0`. Lean verified all three negative refutations affirmatively.

7. **Automated Suite Results**:
   - Output recorded in `/home/goutev/info-geometry-lean/scratch/challenger_suite_results.json`.
   - All 6 tests passed their expected return codes (3 successes, 3 rejections).

---

### 2. Logic Chain

1. **Premise Non-Vacuity**:
   - The theorems in `Hartwig1976SVDMoorePenroseBorder.lean` (`baseA_isMoorePenrose`, `case1Border_isMoorePenrose`, `case1Schur_isMoorePenrose`, `case3Border_isMoorePenrose`, `case3Schur_isMoorePenrose`, `borderPermutation_sq_eq_one`, `borderPermutation_star_eq_self`, `case1_conjugated_border_isMoorePenrose`) take zero premises.
   - Therefore, none of these theorems can hold vacuously or from false premises.
   - The universal lemma `unitConj_isMoorePenrose` has premises `(u : (Mat3 ℚ)ˣ)`, `(A X : Mat3 ℚ)`, `hu_star : star u = (u⁻¹ : Mat3 ℚ)`, and `h : MoorePenrose.IsMoorePenroseInverse A X`. This is instantiated directly with the orthogonal permutation unit `borderPermutationUnit`, where `hu_star` is discharged by `borderPermutation_star_eq_self`.

2. **Kernel Sensitivity & Proof Non-Triviality**:
   - Observations 3, 4, and 5 demonstrate that when any matrix entry is perturbed (e.g. from `5` to `999` or `7/5` to `999`), the candidate proof scripts strictly fail to compile, producing unprovable subgoals (`⊢ False` and `⊢ 999 * (5 / 7) = 1`).
   - This proves that the proof scripts do not bypass the Lean typechecker through proof irrelevance, circular tactics, or trivial tautologies.

3. **Definitional Precision**:
   - Observation 6 establishes that the perturbed statements are strictly false and refuted in the Lean theory, confirming that the arithmetic and algebraic properties of Hartwig's SVD bordered Moore-Penrose packet are exact and sensitive to single-entry perturbations.

4. **Axiom Hygiene**:
   - Observation 2 demonstrates that every theorem depends only on the foundational Lean kernel axioms (`propext`, `Classical.choice`, `Quot.sound`).

---

### 3. Caveats

- The candidate file specifically focuses on exact rational certificates for Hartwig Case 1 (range vectors with nonzero Schur complement) and Case 3 (kernel vector components with full rank jump), plus orthogonal permutation conjugation.
- It does not cover floating-point numerical SVD or the remaining intermediate cases (e.g. Case 2, Case 4, Case 5) from Hartwig 1976, which is documented and expected per the file's design docstring.

---

### 4. Conclusion

- **Verdict**: **APPROVE**.
- The candidate file `/home/goutev/info-geometry-lean/.agents/sandbox_surgical_o1/lean/InfoGeometry/Canonical/Hartwig1976SVDMoorePenroseBorder.lean` is mathematically sound, free of `sorry`, `decide`, or `native_decide`, and exhibits rigorous algebraic sensitivity.
- All negative perturbations are strictly caught and rejected by the Lean kernel.

---

### 5. Verification Method

To independently verify this evaluation, run the automated suite:

```bash
python3 /home/goutev/info-geometry-lean/scratch/run_challenger_suite.py
```

Inspect the generated test artifacts:
- `/home/goutev/info-geometry-lean/scratch/challenger_suite_results.json`
- `/home/goutev/info-geometry-lean/scratch/perturbation_test1_fail.lean`
- `/home/goutev/info-geometry-lean/scratch/perturbation_test2_fail.lean`
- `/home/goutev/info-geometry-lean/scratch/perturbation_test3_fail.lean`
- `/home/goutev/info-geometry-lean/scratch/test_hartwig_adversarial_oracle.lean`
- `/home/goutev/info-geometry-lean/scratch/test_axioms.lean`
