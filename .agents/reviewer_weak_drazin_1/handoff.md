# Independent Review and Adversarial Audit: CampbellMeyerWeakDrazin Candidate

**Reviewer**: teamwork_preview_reviewer (`reviewer_weak_drazin_1`)
**Parent**: `orchestrator_5` (conversation ID: `c310530f-678b-4c1c-948e-b8e7ff7beb38`)
**Target File**: `/home/goutev/info-geometry-lean/.agents/sandbox_weak_drazin_o1/lean/InfoGeometry/Canonical/CampbellMeyerWeakDrazin.lean`
**Diff File**: `/home/goutev/info-geometry-lean/.agents/sandbox_weak_drazin_o1/diffs/weak_drazin.diff`

---

## Review Summary

**Verdict**: **APPROVE**

The candidate file in `.agents/sandbox_weak_drazin_o1/` successfully refactors all 22 instances of `native_decide` to pure kernel-checked Lean 4 tactics (`ext`, `fin_cases`, `simp`, `norm_num`, `calc`, `induction`). The candidate strictly preserves 100% character-level proposition fidelity across all 34 original declarations, introduces zero `sorry` or `admit` tokens, completely purges untrusted `Lean.ofReduceBool` axioms, and compiles cleanly with return code 0 under the shared repository build lock.

---

## 1. Observation

### Exact File Paths and Metrics
- Candidate file: `.agents/sandbox_weak_drazin_o1/lean/InfoGeometry/Canonical/CampbellMeyerWeakDrazin.lean` (334 lines)
- Original file: `lean/InfoGeometry/Canonical/CampbellMeyerWeakDrazin.lean` (263 lines)
- Diff file: `.agents/sandbox_weak_drazin_o1/diffs/weak_drazin.diff` (233 lines)
- CAS certificate: `.agents/sandbox_weak_drazin_o1/CAS/cas_weak_drazin_certificate.py` (136 lines)

### Token Verification
- `native_decide` count in original: **22**
- `native_decide` count in candidate: **0** (100% eliminated)
- `sorry` count in candidate: **0**
- `admit` count in candidate: **0**

### Compilation Under Shared Build Lock
- Command:
  ```python
  from tools.build_lock import acquire_build_lock
  import subprocess
  with acquire_build_lock(None, 'reviewer_weak_drazin_1_compilation_check', block=True):
      res = subprocess.run(
          ['lake', 'env', 'lean', '.agents/sandbox_weak_drazin_o1/lean/InfoGeometry/Canonical/CampbellMeyerWeakDrazin.lean'],
          capture_output=True, text=True
      )
      assert res.returncode == 0
  ```
- Result: Return code `0`. Standard dependency manifest warnings only. Zero errors or linter failures.

### Proposition and Interface Fidelity Check
- Original declarations count: **34**
- Candidate declarations count: **38** (34 original + 4 general structural helper lemmas)
- Missing declarations in candidate: **0**
- Proposition signature mismatches: **0** (Exact character-level equality verified across all 34 original items).
- Definition bodies (`weakA`, `weakWildInverse`, `weakPolynomialInverse`, etc.): Verbatim identical.

### Axiomatic Purity Analysis
- Evaluated `#print axioms` across all 24 refactored declarations via Lean compiler under build lock:
  - `Lean.ofReduceBool` occurrences: **0**
  - `sorryAx` occurrences: **0**
  - Foundational axioms utilized: Strictly standard `[propext, Classical.choice, Quot.sound]`.

---

## 2. Logic Chain

1. **Elimination of Untrusted Oracle**:
   In Lean 4, `native_decide` relies on untrusted compiled code execution, generating proofs that depend on `Lean.ofReduceBool`. By replacing `native_decide` with componentwise matrix extensionality (`ext i j; fin_cases i <;> fin_cases j`) and arithmetic simplification (`simp`, `norm_num`), every computational step is validated directly by the Lean type checker and kernel.

2. **Categorical / Structural Generalization**:
   Instead of unfolding matrix powers under conjugation via brute force, the worker established:
   - `lemma unitConj_mul (u : (Mat3 ℚ)ˣ) (A B : Mat3 ℚ) : unitConj u A * unitConj u B = unitConj u (A * B)`
   - `lemma unitConj_pow (u : (Mat3 ℚ)ˣ) (A : Mat3 ℚ) (n : ℕ) : (unitConj u A) ^ n = unitConj u (A ^ n)`
   - `theorem unitConj_isWeakDrazin (u : (Mat3 ℚ)ˣ) (A B : Mat3 ℚ) (k : ℕ) (h : IsWeakDrazin A B k) : IsWeakDrazin (unitConj u A) (unitConj u B) k`
   This cleanly proves `weak_conjugated_polynomial_inverse_isWeak` by applying `unitConj_isWeakDrazin` to `weakPolynomialInverse_isWeak`, adhering directly to the architectural guidelines in `AGENTS.md`.

3. **Downstream Safety**:
   Dependency grep reveals only one importing module (`lean/InfoGeometry/AllExhaustive.lean:2169`). Because all 34 original declarations retain their exact names, arguments, and proposition signatures, promoting this candidate to the live repository introduces zero downstream regressions.

---

## 3. Adversarial Review & Stress-Testing

**Overall Risk Assessment**: **LOW**

### Assumption Stress-Testing
- **Assumption 1**: Tactic proofs do not silently admit unprovable goals.
  - *Test*: Ran Lean `#print axioms` on all 24 refactored lemmas. Verified that no `sorryAx` exists and only standard axioms are used.
  - *Result*: **PASS**.
- **Assumption 2**: Proposition statements were not subtly weakened or altered.
  - *Test*: Automated AST and character-by-character regex comparison against original file.
  - *Result*: **PASS** (100% exact match).
- **Assumption 3**: Matrix definitions were not altered to trivial matrices.
  - *Test*: Compared definition strings of `weakA`, `weakNilpotentLane`, `weakRegularProjector`, `weakDrazinInverse`, `weakWildInverse`, `weakPolynomialInverse`, `weakProjectiveInverse`, `weakCommutingInverse`, `weakPermutation`.
  - *Result*: **PASS** (100% verbatim identical).
- **Assumption 4**: Integrity of verification artifacts.
  - *Test*: Checked for hardcoded shortcuts, facade proofs, or bypasses.
  - *Result*: **PASS** (Zero integrity violations found).

---

## 4. Findings

### [Minor] Finding 1: Elaboration Time Tradeoff
- **What**: Compilation time for `CampbellMeyerWeakDrazin.lean` changed from ~6.4s (`native_decide`) to ~12.5s (`fin_cases` + `simp`).
- **Where**: Matrix extensionality lemmas expanding 9 entries per theorem across 15 theorems.
- **Why**: Evaluating 9 branches per lemma via `fin_cases` and `norm_num` incurs a minor elaboration cost in the Lean kernel compared to native C VM evaluation.
- **Assessment**: Acceptable. 12.5s is well within normal thresholds for Mathlib matrix proofs, and completely eliminates untrusted VM execution (`Lean.ofReduceBool`), achieving kernel-checked mathematical certification.

---

## 5. Verified Claims

| Claim | Method | Result |
|---|---|---|
| Zero `native_decide` | Token count script / regex | **PASS** (0 remaining) |
| Zero `sorry` / `admit` | Token count script / regex | **PASS** (0 remaining) |
| Lean compilation passes | `lake env lean` under `/tmp/info-geometry-build.lock` | **PASS** (Exit code 0) |
| Axiomatic purity | `#print axioms` query under build lock | **PASS** (No `Lean.ofReduceBool` / `sorryAx`) |
| 100% Proposition fidelity | Character-level signature comparison against original | **PASS** (34/34 match exactly) |
| CAS certificate validity | SymPy verification via `cas_weak_drazin_certificate.py` | **PASS** (All 10 checks passed) |

---

## 6. Caveats

- Dependency manifest warnings (`Qq`, `plausible`, `mathlib`, `doc-gen4` manifest out of date) were observed during compilation, which is expected behavior for the pinned Lean 4.28.1 repository setup and unrelated to this candidate.
- Live repository files were not modified during this review, adhering strictly to the Subagent Sandbox Mandate.

---

## 7. Conclusion

The candidate file `.agents/sandbox_weak_drazin_o1/lean/InfoGeometry/Canonical/CampbellMeyerWeakDrazin.lean` is fully verified, mathematically sound, axiomatically clean, and ready for immediate promotion into the live repository.

**Final Verdict**: **APPROVE**

---

## 8. Verification Method (For Independent Reproduction)

1. **Compilation under build lock**:
   ```bash
   python3 -c "
   from tools.build_lock import acquire_build_lock
   import subprocess
   with acquire_build_lock(None, 'verify-weak-drazin', block=True):
       res = subprocess.run(['lake', 'env', 'lean', '.agents/sandbox_weak_drazin_o1/lean/InfoGeometry/Canonical/CampbellMeyerWeakDrazin.lean'], capture_output=True, text=True)
       assert res.returncode == 0
   "
   ```

2. **Check for zero forbidden tokens**:
   ```bash
   grep -n "native_decide" .agents/sandbox_weak_drazin_o1/lean/InfoGeometry/Canonical/CampbellMeyerWeakDrazin.lean
   grep -n "sorry" .agents/sandbox_weak_drazin_o1/lean/InfoGeometry/Canonical/CampbellMeyerWeakDrazin.lean
   grep -n "admit" .agents/sandbox_weak_drazin_o1/lean/InfoGeometry/Canonical/CampbellMeyerWeakDrazin.lean
   ```

3. **Check CAS certificate**:
   ```bash
   python3 .agents/sandbox_weak_drazin_o1/CAS/cas_weak_drazin_certificate.py
   ```
