# Handoff Report: Elimination of 26 `native_decide` in `Hartwig1976SVDMoorePenroseBorder.lean`

## 1. Observation

1. **Target File Census & Bottleneck Identification**:
   - Live file: `lean/InfoGeometry/Canonical/Hartwig1976SVDMoorePenroseBorder.lean` (213 lines).
   - Baseline count of `native_decide`: **26 occurrences**.
   - Baseline compilation time of live file: **24.29s** via locked runner (`lake env lean`).
   - The 26 `native_decide` occurrences were distributed across 7 distinct mathematical packets:
     * `baseA_isMoorePenrose` (lines 61-64): 4 calls (`A*B*A = A`, `B*A*B = B`, `(A*B)* = A*B`, `(B*A)* = B*A`).
     * `case1Border_isMoorePenrose` (lines 99-102): 4 calls.
     * `case1Schur_isMoorePenrose` (lines 118-121): 4 calls.
     * `case3Border_isMoorePenrose` (lines 148-151): 4 calls.
     * `case3Schur_isMoorePenrose` (lines 167-170): 4 calls.
     * `borderPermutation_sq_eq_one` (line 183): 1 call (`P * P = 1`).
     * `borderPermutation_star_eq_self` (line 188): 1 call (`star P = P`).
     * `case1_conjugated_border_isMoorePenrose` (lines 207-210): 4 calls (conjugated bordered matrix laws under $P$).

2. **Kernel Non-Reduction Mechanism**:
   - Executing standard `decide` on matrix equalities over `ℚ` directly failed in Lean 4's kernel:
     ```
     Tactic `decide` failed for proposition baseA * baseAMP * baseA = baseA
     because its Decidable instance did not reduce to isTrue or isFalse.
     After unfolding instances ... reduction got stuck at:
     match (((fun i => ...).add (List.foldr (fun x1 x2 => x1 + x2) 0 ...)).num, 2) with
     ```
   - Investigation revealed two compounding causes:
     * `Matrix.mul` relies on `Finset.univ.sum` over `Fin n`, which introduces non-reducing proof terms in `Fintype.elems`.
     * `Rat.add` and `Rat.mul` rely on `Rat.normalize` and `Nat.gcd`, which are not marked reducible in the kernel environment, causing VM reliance (`native_decide`) in unoptimized code.

3. **SymPy CAS Verification Results**:
   - Generated and executed `/home/goutev/info-geometry-lean/.agents/sandbox_surgical_o1/CAS/cas_moore_penrose_certificate.py`.
   - Verified exact rational matrix products and integer cleared counterparts ($M_A M_X M_A = d_A d_X M_A$, etc.) for all 7 packets. All assertions passed with exit code 0.
   - Output dumped to `.agents/sandbox_surgical_o1/CAS/moore_penrose_certificates.json`.

4. **Sandbox Implementation and Verification**:
   - Refactored module implemented in:
     `/home/goutev/info-geometry-lean/.agents/sandbox_surgical_o1/lean/InfoGeometry/Canonical/Hartwig1976SVDMoorePenroseBorder.lean`.
   - Compilation result via locked runner:
     `Returncode: 0, 0 linter warnings, 0 errors`.
   - Kernel typechecking profiling:
     10 type-checking operations summing to **2,084 ms (2.084 s)**, satisfying the `<= 15.0 s` requirement.
   - Token audit:
     * `native_decide`: **0**
     * `simpa using`: **0**
     * `sorry`/`admit`: **0**
   - Declaration and proposition fidelity:
     All 24 original declarations and theorems preserved verbatim (0 missing declarations).

---

## 2. Logic Chain

1. **Projector Decomposition & Symmetry Reduction**:
   - The Moore-Penrose equations for a pair $(A, B)$ consist of:
     1. $A B A = A$
     2. $B A B = B$
     3. $(A B)^* = A B$
     4. $(B A)^* = B A$
   - In each case, $P_R = A B$ and $P_L = B A$ are explicit projections.
   - By proving the intermediate product identities $A B = P_R$ and $B A = P_L$ as focused helper lemmas:
     * Self-adjointness $(A B)^* = A B$ and $(B A)^* = B A$ rewrites to $\text{star } P = P$. For concrete diagonal/symmetric matrices over $\mathbb{Q}$, this reduces **definitionally by `rfl`**.
     * Penrose laws $A B A = A$ and $B A B = B$ reduce to $(A B) A = P_R A = A$ and $(B A) B = P_L B = B$. Because $P$ has integer $0/1$ entries, multiplying $P$ with the rational matrix involves no fraction arithmetic, closing via `Fin.sum_univ` expansion without kernel bottlenecks.

2. **Invertible Block Simplification (Case 3)**:
   - For `case3Border` and `case3Schur`, the matrices are invertible and their Moore-Penrose inverses are two-sided algebraic inverses: $A B = 1$ and $B A = 1$.
   - Once $A B = 1$ and $B A = 1$ are established, all four Moore-Penrose equations reduce instantly to:
     * $A B A = 1 \cdot A = A$ via `rw [..., one_mul]`
     * $B A B = 1 \cdot B = B$ via `rw [..., one_mul]`
     * $(A B)^* = \text{star}(1) = 1 = A B$ via `rw [..., star_one]`
     * $(B A)^* = \text{star}(1) = 1 = B A$ via `rw [..., star_one]`
   - This eliminates 8 instances of `native_decide` with pure term rewrites taking $< 0.01\text{ s}$.

3. **Structural Unitary Conjugation Theorem (Case 1 Conjugate)**:
   - Rather than re-running 9-branch case evaluations on the 7-fold product $P A P \cdot P X P \cdot P A P$, we proved a general structural theorem:
     ```lean
     theorem unitConj_isMoorePenrose (u : (Mat3 ℚ)ˣ) (A X : Mat3 ℚ)
         (hu_star : star (u : Mat3 ℚ) = ((u⁻¹ : (Mat3 ℚ)ˣ) : Mat3 ℚ))
         (h : MoorePenrose.IsMoorePenroseInverse A X) :
         MoorePenrose.IsMoorePenroseInverse (unitConj u A) (unitConj u X)
     ```
   - Since `borderPermutationUnit` satisfies `star P = P = P⁻¹`, `case1_conjugated_border_isMoorePenrose` follows by an exact 1-line application of `unitConj_isMoorePenrose`, eliminating 4 `native_decide` calls definitionally and algebraically.

4. **Total Eradication of Axiom `Lean.ofReduceBool`**:
   - `native_decide` introduced an unverified VM evaluation axiom `Lean.ofReduceBool` into the Lean kernel environment.
   - The refactored proofs rely exclusively on standard kernel-verified inferences (`rfl`, `rw`, `simp`, `norm_num`), restoring total axiomatic purity.

---

## 3. Caveats

1. **Sandbox Isolation**:
   - In accordance with the Subagent Sandbox Mandate, the live repository file `lean/InfoGeometry/Canonical/Hartwig1976SVDMoorePenroseBorder.lean` was left completely untouched. The verified changes reside in `.agents/sandbox_surgical_o1/lean/InfoGeometry/Canonical/Hartwig1976SVDMoorePenroseBorder.lean`.
   - Applying the changes to the live tree requires applying `.agents/sandbox_surgical_o1/diffs/candidate.patch` or copying the sandbox file into `lean/InfoGeometry/Canonical/`.

2. **Dependency Imports**:
   - The module imports `Mathlib.Tactic`, `InfoGeometry.Algebra.FiniteSpinAlgebra`, and `InfoGeometry.Canonical.MoorePenrose`. Because Mathlib oleans are precompiled in the repository cache, standard compilation with `lake env lean` takes ~15-18s total process time, of which ~8.5s is olean module loading, and only **2.08s** is kernel type-checking time.

---

## 4. Conclusion

The objective has been completely achieved:
1. All **26 occurrences of `native_decide`** in `Hartwig1976SVDMoorePenroseBorder.lean` have been **eliminated (100% reduction)**.
2. **0 `simpa using`** and **0 `sorry`/`admit`** tokens exist in the candidate file.
3. **100% proposition and declaration fidelity** is preserved: all theorem names, types, and definitions match the live file verbatim.
4. The candidate file compiles with **Exit Code 0**, **0 compiler warnings**, **0 linter errors**, and a **kernel typechecking time of 2.084s** (threshold <= 15.0s).
5. All mathematical properties have been cross-certified by SymPy CAS (`moore_penrose_certificates.json`).
6. All artifacts, diff patches, and audit logs are tracked in git index and organized in `.agents/sandbox_surgical_o1/`.

---

## 5. Verification Method

To independently verify the results:

1. **Verify Token Elimination**:
   ```bash
   f=".agents/sandbox_surgical_o1/lean/InfoGeometry/Canonical/Hartwig1976SVDMoorePenroseBorder.lean"
   echo "native_decide: $(grep -c 'native_decide' $f || true)"  # Expected: 0
   echo "simpa using:   $(grep -c 'simpa using' $f || true)"    # Expected: 0
   echo "sorry/admit:   $(grep -cE '\b(sorry|admit)\b' $f || true)" # Expected: 0
   ```

2. **Verify Single-File Compilation via Locked Runner**:
   ```bash
   python3 -c "
   import sys, subprocess
   from tools.build_lock import acquire_build_lock
   target_file = '.agents/sandbox_surgical_o1/lean/InfoGeometry/Canonical/Hartwig1976SVDMoorePenroseBorder.lean'
   with acquire_build_lock(None, f'check:{target_file}', block=True):
       res = subprocess.run(['lake', 'env', 'lean', target_file], capture_output=True, text=True)
       print('Exit code:', res.returncode)
       if res.stdout: print('Stdout:', res.stdout)
       if res.stderr: print('Stderr:', res.stderr)
       sys.exit(res.returncode)
   "
   # Expected: Exit code: 0, no errors
   ```

3. **Verify Kernel Timing**:
   ```bash
   python3 -c "
   import subprocess, re
   from tools.build_lock import acquire_build_lock
   target_file = '.agents/sandbox_surgical_o1/lean/InfoGeometry/Canonical/Hartwig1976SVDMoorePenroseBorder.lean'
   with acquire_build_lock(None, f'check:{target_file}', block=True):
       res = subprocess.run(['lake', 'env', 'lean', '--profile', target_file], capture_output=True, text=True)
   times = [int(m.group(1)) for line in res.stdout.splitlines() for m in [re.search(r'type checking took (\d+)ms', line)] if m]
   print(f'Kernel time: {sum(times)} ms ({sum(times)/1000:.3f} s)')
   "
   # Expected: Kernel time ~ 2.084 s (<= 15.0 s)
   ```

4. **Verify CAS Certificate Suite**:
   ```bash
   python3 .agents/sandbox_surgical_o1/CAS/cas_moore_penrose_certificate.py
   # Expected: ALL 7 MOORE-PENROSE PACKETS SYMBOLICALLY VERIFIED BY SYMPY.
   ```

5. **Inspect Diff Patch**:
   ```bash
   git diff --stat .agents/sandbox_surgical_o1/diffs/candidate.patch
   cat .agents/sandbox_surgical_o1/diffs/candidate.patch
   ```
