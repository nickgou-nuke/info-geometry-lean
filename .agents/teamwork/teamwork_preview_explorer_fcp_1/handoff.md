# Handoff Report: Phase 0 Exploration & Anatomy of FieldCorrelatorProjection.lean

## 1. Observation

### File Metadata and Location
- **File path**: `lean/InfoGeometry/Detector/FieldCorrelatorProjection.lean`
- **Line count**: 111 lines (112 with trailing newline)
- **File size**: 3,367 bytes
- **Namespace**: `DetectorGeometry.FieldCorrelatorProjection` (Note: internal namespace uses `DetectorGeometry` rather than `InfoGeometry.Detector`, matching sister files in `lean/InfoGeometry/Detector/`)
- **Git history**: Added in commit `46ec2d052d6b099e34593f0d90b930ffb12e65f2` ("Update Lean sources across default targets", 2026-09-20).

### Imports
- Line 1: `import Mathlib.Data.Real.Basic`
- Line 2: `import Mathlib.Tactic` (monolithic import pulling 325 tactic submodules)

### Inbound and Outbound Dependencies
- **Inbound dependencies** (modules importing `FieldCorrelatorProjection.lean`):
  - `grep_search` across `lean/`, `tests/`, `archive/`, `tools/`, and `scripts/` found **zero** inbound imports.
  - Not imported by `lean/InfoGeometry/All.lean` or `lean/InfoGeometry/AllExhaustive.lean`.
  - Compiled by Lake solely because `lakefile.lean` configures:
    ```lean
    lean_lib InfoGeometry where
      globs := #[.andSubmodules `InfoGeometry]
    ```
    which recursively globs all `.lean` files in `lean/InfoGeometry/`.
- **Outbound dependencies** (modules imported by `FieldCorrelatorProjection.lean`):
  - `Mathlib.Data.Real.Basic`
  - `Mathlib.Tactic`

### Complete Inventory of Declarations

| Section | Identifier | Kind | Line(s) | Signature / Definition | Current Proof Strategy |
|---|---|---|---|---|---|
| FieldCorrelator | `FieldCorrelator` | structure | 8–10 | `singleAmplitude : ℝ`, `pairAmplitude : ℝ` | N/A |
| FieldCorrelator | `DetectorProjector` | structure | 12–14 | `singleEfficiency : ℝ`, `pairEfficiency : ℝ` | N/A |
| FieldCorrelator | `projectSingle` | def | 16–17 | `(detector : DetectorProjector) (field : FieldCorrelator) : ℝ` | `detector.singleEfficiency * field.singleAmplitude` |
| FieldCorrelator | `projectPair` | def | 19–20 | `(detector : DetectorProjector) (field : FieldCorrelator) : ℝ` | `detector.pairEfficiency * field.pairAmplitude` |
| FieldCorrelator | `projector_single_linear` | theorem | 22–29 | Linearity of `projectSingle` on linear combinations | `by simp [projectSingle]; ring` |
| FieldCorrelator | `projector_pair_bilinear_scale` | theorem | 31–34 | `(ε₁ * ε₂) * (a * b) = (ε₁ * a) * (ε₂ * b)` | `by ring` |
| ModeProjection | `modeTrace` | def | 39–40 | `(monopole oscillatory : ℝ) : ℝ := monopole + 0 * oscillatory` | N/A |
| ModeProjection | `oscillatory_modes_annihilated` | theorem | 41–43 | `modeTrace monopole oscillatory = monopole` | `by simp [modeTrace]` |
| ModeProjection | `modeTrace_linear` | theorem | 45–49 | `modeTrace` distributes over linear combination | `by simp [modeTrace]` |
| RankHierarchy | `singlesCount` | def | 54–55 | `(N₀ ε X : ℝ) : ℝ := N₀ * ε * X` | N/A |
| RankHierarchy | `coincidenceCount` | def | 56–57 | `(N₀ K X : ℝ) : ℝ := N₀ * K * X ^ 2` | N/A |
| RankHierarchy | `coincidence_is_rank_two` | theorem | 58–60 | `coincidenceCount N₀ K X = (N₀ * K) * X ^ 2` | `by rfl` |
| RankHierarchy | `square_root_coordinate_is_linear` | theorem | 62–64 | `singlesCount N₀ ε X = (N₀ * ε) * X` | `by rfl` |
| RankHierarchy | `detector_projection_parabola` | theorem | 66–69 | `coincidenceCount N₀ K X = (N₀ * K) * X ^ 2` | `by rfl` (DUPLICATE of `coincidence_is_rank_two`) |
| CausalPoset | `Archetype` | inductive | 74–80 | 5 nullary constructors: `fieldCorrelator`, `detectorProjector`, `modeNullspace`, `rankHierarchy`, `scaleInvariantObservable` | `deriving DecidableEq, Repr` |
| CausalPoset | `rank` | def | 82–88 | `Archetype → Nat` (values: 195, 196, 197, 198, 199) | Pattern match |
| CausalPoset | `causallyPrecedes` | def | 89–90 | `(a b : Archetype) : Prop := rank a ≤ rank b` | N/A |
| CausalPoset | `causal_refl` | theorem | 91–92 | `causallyPrecedes a a` | `le_rfl` |
| CausalPoset | `causal_trans` | theorem | 93–96 | `causallyPrecedes a b → causallyPrecedes b c → causallyPrecedes a c` | `by exact Nat.le_trans` |
| CausalPoset | `causal_antisymm` | theorem | 97–101 | `causallyPrecedes a b → causallyPrecedes b a → a = b` | `by intro hab hba; cases a <;> cases b <;> simp [causallyPrecedes, rank] at hab hba ⊢` |
| CausalPoset | `canonical_chain` | theorem | 102–108 | 4-way conjunct chain of `causallyPrecedes` | `by norm_num [causallyPrecedes, rank]` |

### Investigation of the "10-Hour Compile Gap"
- Running `python3 tools/infra/compute_all_bottlenecks.py` lists `InfoGeometry.Detector.FieldCorrelatorProjection` at the very top with:
  `Delta T = 36529.82 seconds` (~10.15 hours).
- Examination of the filesystem `.olean` modification times reveals:
  - `InfoGeometry.Audit.olean`: mtime `1789802241.4171672` (2026-09-20 10:24:01 UTC)
  - `InfoGeometry.Detector.FieldCorrelatorProjection.olean`: mtime `1789838771.2409873` (2026-09-20 20:32:51 UTC)
  - `InfoGeometry.Motivic.PolylogarithmicUnipotentMotive.olean`: mtime `1789838771.2608943` (2026-09-20 20:32:51 UTC, +0.02s)
  - `InfoGeometry.Detector.InertialFrameUniqueness.olean`: mtime `1789838771.2808013` (2026-09-20 20:32:51 UTC, +0.02s)
- **Direct Cause**: The script `compute_all_bottlenecks.py` calculates $\Delta t$ purely as the difference between adjacent `.olean` modification timestamps (`olean_files[i].mtime - olean_files[i-1].mtime`). A 10-hour machine pause or gap between compile runs occurred after `InfoGeometry.Audit` finished. When the build resumed, `FieldCorrelatorProjection` was the first file written, causing the script to erroneously attribute the entire 10-hour inter-build hiatus to this module.

---

## 2. Logic Chain

1. **Bottleneck Attribution vs. Structural Quality**:
   - Observation: `compute_all_bottlenecks.py` computes $\Delta t = 36529.82$ seconds due to a wall-clock timestamp gap, not 10 hours of CPU computation.
   - Deduction: The file does not actually consume 10 hours of CPU time to compile. However, it was flagged globally as the #1 repository bottleneck, and the user explicitly mandated its surgical compression and refactoring.
2. **Heavy Imports Inefficiency**:
   - Observation: Line 2 imports `Mathlib.Tactic`, which exposes over 325 tactic submodules into the compile environment.
   - Deduction: Only `ring` and `norm_num` tactics are invoked. If `norm_num` is replaced by `by decide`, the only Mathlib tactic required is `Mathlib.Tactic.Ring`. Pruning `Mathlib.Tactic` drastically reduces elaboration environment memory footprint.
3. **Redundant Code Inefficiency**:
   - Observation: Lines 58–60 (`coincidence_is_rank_two`) and lines 66–69 (`detector_projection_parabola`) have identical signatures `(N₀ K X : ℝ) : coincidenceCount N₀ K X = (N₀ * K) * X ^ 2` and identical proofs `by rfl`.
   - Deduction: `detector_projection_parabola` is a verbatim duplicate definition that can be eliminated or aliased.
4. **Brute-Force Tactic Storm in Poset Antisymmetry**:
   - Observation: Line 100 uses `cases a <;> cases b <;> simp [causallyPrecedes, rank] at hab hba ⊢`. This produces $5 \times 5 = 25$ subgoals and runs the `simp` rewriter on all 25 cases.
   - Deduction: Because `rank` is strictly monotonic and distinct for all 5 constructors, `hab : rank a ≤ rank b` and `hba : rank b ≤ rank a` yield `rank a = rank b` via `Nat.le_antisymm hab hba`. The equality `rank a = rank b` allows proving injectivity `rank_injective : Function.Injective rank` once, reducing `causal_antisymm` to a single term application: `rank_injective (Nat.le_antisymm hab hba)`.
5. **Arithmetic Tactic in Canonical Chain**:
   - Observation: Line 107 invokes `norm_num [causallyPrecedes, rank]`.
   - Deduction: `causallyPrecedes` on concrete constructors evaluates to `195 ≤ 196 ∧ 196 ≤ 197 ∧ 197 ≤ 198 ∧ 198 ≤ 199`, which is decidable in the core Lean kernel via `by decide` with $O(1)$ complexity and zero tactic overhead.
6. **Bilinear Scale Identity**:
   - Observation: Line 33 proves `(ε₁ * ε₂) * (a * b) = (ε₁ * a) * (ε₂ * b)` using `ring`.
   - Deduction: This is Mathlib's `mul_mul_mul_comm ε₁ ε₂ a b`, solvable with `exact mul_mul_mul_comm ε₁ ε₂ a b` in $O(1)$.

---

## 3. Caveats

1. **No Live Edits**: In accordance with Phase 0 exploration and the Subagent Sandbox Mandate, no live repository files were modified. All refactoring proposals must be implemented in `.agents/sandbox_correlator/` first.
2. **Sequential Build Lock Active**: An existing background `lake build` process (PID 1850) is active. No concurrent compilation or lake commands were run during this discovery phase.
3. **Downstream Isolation**: Since no other module currently imports `FieldCorrelatorProjection.lean`, changes to this file will not break downstream builds, making it safe for surgical compression and potential wiring into `InfoGeometry.AllExhaustive`.

---

## 4. Conclusion

- `FieldCorrelatorProjection.lean` is a clean, 111-line leaf module with 3 types, 7 definitions, and 11 theorems across 4 logical sections (`FieldCorrelator`, `ModeProjection`, `RankHierarchy`, `CausalPoset`).
- Its presence at the top of `compute_all_bottlenecks.py` (36,529.82 seconds) was an artifact of inter-build machine suspend time rather than 10 hours of CPU computation.
- Despite this artifact, the file contains multiple clear targets for OpenGauss `/golf` and `/refactor` compression:
  1. **Prune `import Mathlib.Tactic`** -> replace with `import Mathlib.Tactic.Ring` or eliminate tactics altogether.
  2. **Eliminate duplicate theorem** -> `detector_projection_parabola` is redundant with `coincidence_is_rank_two`.
  3. **Refactor 25-case brute force in `causal_antisymm`** -> replace `cases a <;> cases b <;> simp` with an injectivity lemma `rank_injective` and `Nat.le_antisymm`.
  4. **Replace `norm_num` with `by decide`** -> $O(1)$ kernel decision for `canonical_chain`.
  5. **Replace `ring` with `mul_mul_mul_comm`** -> $O(1)$ term proof for `projector_pair_bilinear_scale`.
  6. **Add Python CAS certificate script** in `.agents/sandbox_correlator/CAS/cas_field_correlator_certificate.py` to verify rank orderings, projector algebra, and linearities.

---

## 5. Verification Method

1. **Inspect Target File**:
   `view_file` or `wc -l lean/InfoGeometry/Detector/FieldCorrelatorProjection.lean` confirms 111 lines and exact declaration list.
2. **Verify Inbound/Outbound Module References**:
   `grep -rn "FieldCorrelatorProjection" lean/` confirms zero inbound imports.
3. **Verify Timestamp Hiatus in Build History**:
   Inspect `.lake/build/lib/lean` mtimes using `python3 tools/infra/compute_all_bottlenecks.py` and Python `os.path.getmtime` to confirm the 36,529s gap occurred between `InfoGeometry.Audit.olean` (1789802241) and `FieldCorrelatorProjection.olean` (1789838771).
