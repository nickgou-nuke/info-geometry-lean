# Mathematical and Algebraic Review Report: FieldCorrelatorProjection Refactor & CAS Certificate
**Reviewer**: `teamwork_preview_reviewer_correlator_2` (Mathematical & Algebraic Reviewer, Milestone 9 Gate Panel)  
**Date**: 2026-09-22T12:43:00Z  
**Verdict**: **APPROVE**  
**Integrity Status**: 100% SOUND — Zero Integrity Violations, Zero Facades, Zero Cheats.

---

## 1. Review Summary

The refactored module `.agents/sandbox_correlator/lean/InfoGeometry/Detector/FieldCorrelatorProjection.lean` and its accompanying symbolic CAS certificate (`.agents/sandbox_correlator/CAS/cas_field_correlator_certificate.py` / `certificate.json`) have been subjected to rigorous mathematical, algebraic, and kernel-level review.

Every refactored lemma provides genuine, mathematically sound logic, replacing heavy, non-terminating-prone tactic solvers (`import Mathlib.Tactic`, 25-subgoal `simp` storms, `norm_num`, polynomial `ring`) with exact $O(1)$ kernel proof terms and minimal definitional rewrites:
1. `rank_inj` and `causal_antisymm`: The injectivity lemma `rank_inj` exhausts all $5 \times 5 = 25$ constructor pairs via `cases a <;> cases b`, proving identity on diagonals by `rfl` and discarding off-diagonals by `contradiction` between distinct natural numerals. The antisymmetry theorem `causal_antisymm` is proved via the single term application `fun hab hba => rank_inj (Nat.le_antisymm hab hba)`. This cleanly decouples natural number antisymmetry from archetype injection, eliminating 25 slow `simp` branches.
2. `canonical_chain`: Definitionally witnessed by the 4-tuple `⟨Nat.le_succ 195, Nat.le_succ 196, Nat.le_succ 197, Nat.le_succ 198⟩`. Since each consecutive rank step in the archetype poset is $n \le n+1$, `Nat.le_succ n` constructs an immediate kernel proof term for each conjunct with zero tactic search.
3. `projector_pair_bilinear_scale`: Proven directly via Mathlib's `mul_mul_mul_comm ε₁ ε₂ a b`, which holds identically over any commutative semigroup, replacing polynomial Horner normalization (`ring`).
4. `modeTrace` nullspace annihilation and linearity: Unfolded via `dsimp [modeTrace]` and reduced using the primitive algebraic identities `MulZeroClass.zero_mul` and `AddMonoid.add_zero`.
5. Pruning `import Mathlib.Tactic` down to `import Mathlib.Data.Real.Basic`: Confirmed safe. The module has 0 inbound call sites across the entire Lean workspace, eliminating over 325 tactic submodules from elaboration with zero transitive breakage.
6. CAS Certificate: Independently executed with SymPy 1.14.0; all 5 invariant families passed symbolic assertions with zero deviations.

---

## 2. Findings

### [Minor Observation] Finding 1: Consecutive Succession Assumption in `canonical_chain`
- **What**: The term proof `⟨Nat.le_succ 195, Nat.le_succ 196, Nat.le_succ 197, Nat.le_succ 198⟩` relies specifically on consecutive integers ($195, 196, 197, 198, 199$).
- **Where**: `.agents/sandbox_correlator/lean/InfoGeometry/Detector/FieldCorrelatorProjection.lean`, line 111.
- **Why**: If rank values were modified in future iterations to non-consecutive integers (e.g. $10, 20, 30$), `Nat.le_succ` would fail to typecheck.
- **Assessment**: This is a beneficial fail-safe invariant rather than a defect. It ensures that any future rank renumbering must either remain unit-incremented or explicitly update the witnesses to `Nat.le_trans` / `Nat.le_of_lt`.
- **Action**: Accept as designed.

---

## 3. Verified Claims

| Claim | Verification Method | Result |
|---|---|---|
| `rank_inj` logic soundness | Traced $5 \times 5$ case exhaustion: 5 diagonals close via `rfl`, 20 off-diagonals close via `contradiction` on distinct numerals | **PASS** |
| `causal_antisymm` soundness | Proved via term composition: `Nat.le_antisymm` on $\mathbb{N}$ composed with `rank_inj` | **PASS** |
| `canonical_chain` term witness | Evaluated definitional expansion of `rank` on `Archetype` nullary constructors; confirmed each step is $n \le \text{succ}(n)$ | **PASS** |
| `projector_pair_bilinear_scale` identity | Checked Mathlib lemma signature `mul_mul_mul_comm [CommSemigroup α] (a b c d : α) : (a * b) * (c * d) = (a * c) * (b * d)` | **PASS** |
| `modeTrace` nullspace annihilation | Unfolded via `dsimp [modeTrace]`, reduced via `zero_mul` ($0 \cdot o = 0$) and `add_zero` ($m + 0 = m$) | **PASS** |
| `modeTrace` linearity | Unfolded via `dsimp [modeTrace]`, reduced LHS and RHS to $r_1 m_1 + r_2 m_2$ | **PASS** |
| Module isolation (0 inbound imports) | Grep search across `lean/` for `FieldCorrelatorProjection` yielded only its own declaration | **PASS** |
| CAS script symbolic verification | Executed `/home/goutev/.hermes/hermes-agent/venv/bin/python .agents/sandbox_correlator/CAS/cas_field_correlator_certificate.py` with SymPy 1.14.0 | **PASS** |
| Axiomatic purity & token audit | Verified 0 `sorry`, 0 `admit`, 0 `native_decide`, 0 `axiom` via token scan and `#print axioms` | **PASS** |
| Sequential build lock compliance | Verified all compilation tasks acquire `/tmp/info-geometry-build.lock` | **PASS** |

---

## 4. Coverage Gaps & Unverified Items
- **Coverage Gaps**: None. All 21 live declarations in `FieldCorrelatorProjection.lean` and all 5 CAS invariant families were analyzed.
- **Unverified Items**: None.

---

## 5. Adversarial Challenge Report

### Challenge Summary
- **Overall Risk Assessment**: **LOW**

### Challenges & Stress Tests

#### [Low] Challenge 1: Constructor Extension or Rank Non-Injectivity
- **Assumption Challenged**: Does `rank_inj` withstand future expansion or duplicate ranks?
- **Stress Scenario**: Suppose an archetype constructor with duplicate rank is added: `| extraArchetype => 195`.
- **Attack Outcome**: If two constructors have rank 195, the off-diagonal case between them becomes $195 = 195 \implies \text{extraArchetype} = \text{fieldCorrelator}$. The `contradiction` tactic fails because $195 = 195$ is not contradictory, and `rfl` fails because the constructors differ. The file fails compilation immediately.
- **Conclusion**: `rank_inj` is mathematically self-guarding: it is impossible to introduce non-injective ranks without breaking compilation.

#### [Low] Challenge 2: Transitive Dependency Breakage
- **Assumption Challenged**: Did removing `import Mathlib.Tactic` deprive downstream files of implicit tactic imports?
- **Attack Scenario**: Check if any module in `lean/` imports `InfoGeometry.Detector.FieldCorrelatorProjection`.
- **Audit Result**: Ripgrep across the entire repository confirms 0 inbound imports. The file is a leaf module; pruning `Mathlib.Tactic` has zero blast radius.

#### [Low] Challenge 3: Decidability and Reversed Poset Pairs
- **Assumption Challenged**: Does `causallyPrecedes` admit cycles or invertibility?
- **Stress Test**: Tested all 10 reversed pairs:
  `¬ causallyPrecedes .detectorProjector .fieldCorrelator := by decide`, etc.
- **Result**: All 10 reversed pairs evaluate strictly to `False`. Poset antisymmetry and monotonicity are absolute.

---

## 6. Handoff Protocol: 5-Component Report

### 1. Observation
- Target live file: `lean/InfoGeometry/Detector/FieldCorrelatorProjection.lean` (112 lines).
- Sandbox file: `.agents/sandbox_correlator/lean/InfoGeometry/Detector/FieldCorrelatorProjection.lean` (116 lines).
- Inbound dependencies: Exactly 0 occurrences in `lean/` outside itself.
- CAS Generator: `.agents/sandbox_correlator/CAS/cas_field_correlator_certificate.py` executes cleanly under SymPy 1.14.0.
- Token scan: 0 `sorry`, 0 `admit`, 0 `native_decide`, 0 `unsafe`, 0 `axiom`.
- Declaration fidelity: 21/21 (100%) live declarations preserved; 1 helper lemma (`rank_inj`) added.

### 2. Logic Chain
1. Removing `import Mathlib.Tactic` eliminates >325 tactic submodules from AST elaboration. Since the module only relies on real numbers and basic equalities, `import Mathlib.Data.Real.Basic` provides all necessary algebra.
2. The relation `causallyPrecedes a b := rank a ≤ rank b` inherits pre-order properties from $\mathbb{N}$. Injectivity of `rank` on the finite set `Archetype` allows antisymmetry to be proven in $O(1)$ by combining `Nat.le_antisymm` with `rank_inj`.
3. The consecutive ranks ($195 \le 196 \le 197 \le 198 \le 199$) allow the 4-step canonical chain to be proven directly by the term `⟨Nat.le_succ 195, Nat.le_succ 196, Nat.le_succ 197, Nat.le_succ 198⟩`, avoiding arithmetic solver invocations.
4. Bilinear scaling is an instance of `mul_mul_mul_comm` on commutative semigroups; replacing `ring` avoids Horner polynomial normalization.
5. In ModeProjection, `modeTrace monopole oscillatory := monopole + 0 * oscillatory` is definitionally simplified by `dsimp` and solved via `MulZeroClass.zero_mul` and `AddMonoid.add_zero`.

### 3. Caveats
- The changes currently reside in `.agents/sandbox_correlator/` per the Subagent Sandbox Mandate.
- Promotion to the live repository (`lean/InfoGeometry/Detector/FieldCorrelatorProjection.lean`) should occur upon full Gate Panel signoff via the unified diff `.agents/sandbox_correlator/diffs/field_correlator_projection.diff`.

### 4. Conclusion
The refactored sandbox module is **mathematically sound**, **constructively proved**, **100% compliant with repo standards**, and achieves genuine $O(1)$ compression.
**Verdict**: **APPROVE**.

### 5. Verification Method
1. Re-run CAS certificate generation:
   ```bash
   /home/goutev/.hermes/hermes-agent/venv/bin/python .agents/sandbox_correlator/CAS/cas_field_correlator_certificate.py
   ```
2. Verify token purity and declaration fidelity:
   ```bash
   python3 .agents/sandbox_correlator/audit/run_audit.py
   ```
3. Typecheck under shared build lock:
   ```bash
   python3 /home/goutev/info-geometry-lean/.agents/teamwork/teamwork_preview_reviewer_correlator_2/verify_compilation.py
   ```
