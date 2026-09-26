# Milestone 9 Review Report: FieldCorrelatorProjection Compression

- **Agent**: `teamwork_preview_reviewer_correlator_1` (Reviewer & Adversarial Critic)
- **Role**: Code and Theorem Reviewer for the Milestone 9 Gate Panel
- **Working Directory**: `/home/goutev/info-geometry-lean/.agents/teamwork/teamwork_preview_reviewer_correlator_1`
- **Target Module**: `lean/InfoGeometry/Detector/FieldCorrelatorProjection.lean`
- **Sandbox Directory**: `/home/goutev/info-geometry-lean/.agents/sandbox_correlator`
- **Timestamp**: 2026-09-22T12:40:00Z
- **Verdict**: **APPROVE**

---

## 1. Observation

1. **Sandbox & Live File Comparison**:
   - Live File: `lean/InfoGeometry/Detector/FieldCorrelatorProjection.lean` (112 lines, commit `46ec2d052d6b099e34593f0d90b930ffb12e65f2`).
   - Sandbox File: `.agents/sandbox_correlator/lean/InfoGeometry/Detector/FieldCorrelatorProjection.lean` (116 lines).
   - Unified Diff: `.agents/sandbox_correlator/diffs/field_correlator_projection.diff`. Tested independently via `patch --dry-run -p0 lean/InfoGeometry/Detector/FieldCorrelatorProjection.lean < .agents/sandbox_correlator/diffs/field_correlator_projection.diff` which succeeded with returncode 0 and no fuzz.

2. **Declaration & Signature Fidelity (21/21 Live Declarations Preserved)**:
   - Evaluated all 21 original declarations via automated AST and regex parsing:
     - `FieldCorrelator`: structure (Exact match)
     - `DetectorProjector`: structure (Exact match)
     - `projectSingle`: def (Exact match)
     - `projectPair`: def (Exact match)
     - `projector_single_linear`: theorem (Exact match)
     - `projector_pair_bilinear_scale`: theorem (Exact match)
     - `modeTrace`: def (Exact match)
     - `oscillatory_modes_annihilated`: theorem (Exact match)
     - `modeTrace_linear`: theorem (Exact match)
     - `singlesCount`: def (Exact match)
     - `coincidenceCount`: def (Exact match)
     - `coincidence_is_rank_two`: theorem (Exact match)
     - `square_root_coordinate_is_linear`: theorem (Exact match)
     - `detector_projection_parabola`: theorem (Exact match)
     - `Archetype`: inductive (Exact match)
     - `rank`: def (Exact match)
     - `causallyPrecedes`: def (Exact match)
     - `causal_refl`: theorem (Exact match)
     - `causal_trans`: theorem (Exact match)
     - `causal_antisymm`: theorem (Exact match)
     - `canonical_chain`: theorem (Exact match)
   - New Declarations: Exactly 1 helper lemma added (`rank_inj : ∀ {a b : Archetype}, rank a = rank b → a = b`), which modularly factors constructor injectivity for `Archetype`.
   - Fidelity rate: 100.0% (21/21 preserved, 0 missing).

3. **Compilation & Script Execution**:
   - Independent execution of `.agents/sandbox_correlator/scripts/verify_sandbox.sh` completed successfully with return code 0.
   - SymPy CAS certificate generated and validated across all 5 invariant classes (`.agents/sandbox_correlator/CAS/certificate.json`).
   - Lean typechecking under shared repository build lock (`lake env lean --threads 1`) compiled cleanly with:
     - 0 compiler errors
     - 0 linter warnings
     - 0 `sorry`
     - 0 `admit`
     - 0 `native_decide`
     - 0 `unsafe`
     - 0 non-standard axioms (`sorryAx`, `ofReduceBool`)

4. **Import & Tactic Refactoring**:
   - Removed `import Mathlib.Tactic` (which pulls >325 tactic submodules, consuming >5.5 GB virtual memory).
   - Retained only `import Mathlib.Data.Real.Basic`.
   - Post-import elaboration measured at ~520–750 ms and tactic execution at 518 ms (down from heavy multi-gigabyte elaboration cycles).

5. **Repository Downstream Invariants**:
   - Ripgrep search confirmed zero downstream modules importing `InfoGeometry.Detector.FieldCorrelatorProjection`. It is an isolated leaf component.

---

## 2. Logic Chain

1. **Import Pruning & Module Modularity**:
   - *Observation*: The module only manipulates basic real numbers (`ℝ`) and natural number comparisons (`Nat.le`).
   - *Logic*: The omnibus import `import Mathlib.Tactic` was completely gratuitous. Pruning to `Mathlib.Data.Real.Basic` eliminates massive AST deserialization without depriving the module of necessary algebraic lemmas (`mul_add`, `mul_left_comm`, `mul_mul_mul_comm`).

2. **Antisymmetry Refactoring**:
   - *Observation*: The original proof of `causal_antisymm` relied on `cases a <;> cases b <;> simp [causallyPrecedes, rank] at hab hba ⊢`, triggering a 25-subgoal rewriting storm.
   - *Logic*: Since `causallyPrecedes a b` is defined as `rank a ≤ rank b`, `hab` and `hba` imply `rank a = rank b` by `Nat.le_antisymm`. Because `rank` maps the 5 nullary constructors of `Archetype` injectively to {195, 196, 197, 198, 199}, `rank a = rank b → a = b` is provable once in `rank_inj` by structural exhaustion (`cases a <;> cases b <;> first | rfl | contradiction`).
   - *Conclusion*: Proving `causal_antisymm` via `fun hab hba => rank_inj (Nat.le_antisymm hab hba)` replaces heavy `simp` tactic searches with a direct, constructive proof term.

3. **Canonical Chain Definitional Witness**:
   - *Observation*: The live file proved `canonical_chain` via `norm_num [causallyPrecedes, rank]`.
   - *Logic*: The goal consists of the four conjuncts `195 ≤ 196`, `196 ≤ 197`, `197 ≤ 198`, and `198 ≤ 199`. For any natural $n$, $n \le n + 1$ is definitionally witnessed by `Nat.le_succ n`.
   - *Conclusion*: Providing `⟨Nat.le_succ 195, Nat.le_succ 196, Nat.le_succ 197, Nat.le_succ 198⟩` solves the goal in $O(1)$ kernel time with zero tactics.

4. **Bilinear Scaling Term Proof**:
   - *Observation*: `projector_pair_bilinear_scale` proves `(ε₁ * ε₂) * (a * b) = (ε₁ * a) * (ε₂ * b)`.
   - *Logic*: This equality is an instance of `mul_mul_mul_comm` from Mathlib's commutative semigroup hierarchy.
   - *Conclusion*: `mul_mul_mul_comm ε₁ ε₂ a b` closes the theorem directly, removing invocation of the `ring` tactic.

5. **Deduplication of Parabola Theorem**:
   - *Observation*: `detector_projection_parabola` was a verbatim duplicate of `coincidence_is_rank_two`.
   - *Logic*: Replacing the `rfl` proof script with `coincidence_is_rank_two N₀ K X` establishes explicit lemma reuse while maintaining signature equivalence.

6. **Integrity & Adversarial Audit**:
   - *Check*: Did the worker hardcode test results, fake proofs, or bypass verification?
   - *Finding*: No hardcoded constants or shortcuts were introduced. The constants (195–199) and formulas were already in the original repository file. Lean's kernel independently checked all proofs. No `sorry`, `admit`, `native_decide`, or non-standard axioms exist.

---

## 3. Caveats

1. **Live Repo Isolation**:
   - Per the Subagent Sandbox Mandate, the live file `lean/InfoGeometry/Detector/FieldCorrelatorProjection.lean` has NOT been modified yet.
   - Promotion should take place during Milestone 12 after the full Gate Panel convenes.

2. **Sequential Build Lock Discipline**:
   - All tests and compilation runs must continue to use `/tmp/info-geometry-build.lock` via `tools.build_lock` or `tools/infra/run_locked_lake_build.py` to prevent lock contention and memory exhaustion on the host.

3. **Downstream Coupling**:
   - Currently, no files import `FieldCorrelatorProjection`. If downstream files are added in future milestones, they will benefit from importing a lightweight module instead of pulling in `Mathlib.Tactic`.

---

## 4. Conclusion

- **Verdict**: **APPROVE**.
- The worker `teamwork_preview_worker_correlator_1` has delivered an exemplary, high-integrity refactoring.
- All 21 original declarations are preserved with identical signatures.
- Omnibus `Mathlib.Tactic` is completely eliminated.
- 0 errors, 0 warnings, 0 `sorry`, 0 `native_decide`.
- The unified diff is clean, minimal, and verified.
- The CAS certificate script and E2E verification pipeline pass completely.

---

## 5. Verification Method

To independently reproduce and verify this review:

1. **Verify Declaration Signatures and AST Parity**:
   ```bash
   python3 .agents/sandbox_correlator/audit/run_audit.py
   cat .agents/sandbox_correlator/audit/audit_declaration_fidelity.log
   ```

2. **Verify Forbidden Tokens**:
   ```bash
   python3 scratch/challenger_correlator_2/check_tokens.py
   cat .agents/sandbox_correlator/audit/audit_token_scan.log
   ```

3. **Verify Clean Patch Application**:
   ```bash
   patch --dry-run -p0 lean/InfoGeometry/Detector/FieldCorrelatorProjection.lean < .agents/sandbox_correlator/diffs/field_correlator_projection.diff
   ```

4. **Verify Lean 4 Compilation Under Build Lock**:
   ```bash
   python3 -c '
   import sys, os, subprocess
   sys.path.insert(0, os.path.abspath("."))
   from tools.build_lock import acquire_build_lock
   with acquire_build_lock(None, "reviewer_check", block=True):
       res = subprocess.run(["lake", "env", "lean", "--threads", "1", ".agents/sandbox_correlator/lean/InfoGeometry/Detector/FieldCorrelatorProjection.lean"])
       assert res.returncode == 0
   print("Lean typechecking SUCCESS: 0 errors")
   '
   ```

5. **Run Full Sandbox Verification Script**:
   ```bash
   bash .agents/sandbox_correlator/scripts/verify_sandbox.sh
   ```
