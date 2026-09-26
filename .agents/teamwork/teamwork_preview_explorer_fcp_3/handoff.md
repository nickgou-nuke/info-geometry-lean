# Phase 0 Architecture Report: FieldCorrelatorProjection Compression

## 1. Observation

- **Target File**: `lean/InfoGeometry/Detector/FieldCorrelatorProjection.lean` (111 lines, commit `46ec2d052d6b099e34593f0d90b930ffb12e65f2`).
- **Imports**:
  ```lean
  1: import Mathlib.Data.Real.Basic
  2: import Mathlib.Tactic
  ```
  `Mathlib.Tactic` is an omnibus meta-library loading hundreds of heavy tactic implementations, macros, and thousands of transitive declarations into memory.
- **Section 1 (FieldCorrelator)**:
  Lines 22-30:
  ```lean
  theorem projector_single_linear (detector : DetectorProjector)
      (field₁ field₂ : FieldCorrelator) (r₁ r₂ : ℝ) :
      projectSingle detector
          ⟨r₁ * field₁.singleAmplitude + r₂ * field₂.singleAmplitude,
            r₁ * field₁.pairAmplitude + r₂ * field₂.pairAmplitude⟩ =
        r₁ * projectSingle detector field₁ + r₂ * projectSingle detector field₂ := by
    simp [projectSingle]
    ring
  ```
  Lines 31-34:
  ```lean
  theorem projector_pair_bilinear_scale (ε₁ ε₂ a b : ℝ) :
      (ε₁ * ε₂) * (a * b) = (ε₁ * a) * (ε₂ * b) := by
    ring
  ```
  `ring` tactic runs polynomial normal form reification. However, `projector_pair_bilinear_scale` is an exact instance of Mathlib's `mul_mul_mul_comm`.
- **Section 2 (ModeProjection)**:
  Lines 41-49:
  ```lean
  theorem oscillatory_modes_annihilated (monopole oscillatory : ℝ) :
      modeTrace monopole oscillatory = monopole := by
    simp [modeTrace]

  theorem modeTrace_linear (m₁ o₁ m₂ o₂ r₁ r₂ : ℝ) :
      modeTrace (r₁ * m₁ + r₂ * m₂) (r₁ * o₁ + r₂ * o₂) =
        r₁ * modeTrace m₁ o₁ + r₂ * modeTrace m₂ o₂ := by
    simp [modeTrace]
  ```
  Both invoke the general `simp` rewriter, which traverses the global simp set for rewrites that are definitionally reducible via `zero_mul` and `add_zero`.
- **Section 3 (RankHierarchy)**:
  Lines 58-69:
  `coincidence_is_rank_two`, `square_root_coordinate_is_linear`, and `detector_projection_parabola` are proven by `rfl`. `detector_projection_parabola` has the exact same statement as `coincidence_is_rank_two`.
- **Section 4 (CausalPoset)**:
  Lines 74-88: `Archetype` has 5 inductive constructors (`fieldCorrelator`, `detectorProjector`, `modeNullspace`, `rankHierarchy`, `scaleInvariantObservable`) mapped to ranks 195, 196, 197, 198, 199.
  Lines 97-101:
  ```lean
  theorem causal_antisymm {a b : Archetype} :
      causallyPrecedes a b → causallyPrecedes b a → a = b := by
    intro hab hba
    cases a <;> cases b <;> simp [causallyPrecedes, rank] at hab hba ⊢
  ```
  `cases a <;> cases b` generates $5 \times 5 = 25$ subgoals. For each subgoal, `simp [causallyPrecedes, rank] at hab hba ⊢` searches hypotheses and goal lemmas, refuting 20 off-diagonal arithmetic inequalities through repeated tactic elaboration.
  Lines 102-108:
  ```lean
  theorem canonical_chain :
      causallyPrecedes .fieldCorrelator .detectorProjector ∧
      causallyPrecedes .detectorProjector .modeNullspace ∧
      causallyPrecedes .modeNullspace .rankHierarchy ∧
      causallyPrecedes .rankHierarchy .scaleInvariantObservable := by
    norm_num [causallyPrecedes, rank]
  ```
  `norm_num` runs an arithmetic decision procedure, whereas the 4 relations are definitionally $195 \le 196, 196 \le 197, 197 \le 198, 198 \le 199$, which match `Nat.le_succ n`.
- **Tooling & Environment Observations**:
  - OpenGauss commands (`/golf`, `/refactor`) at `.agents/plugins/opengauss/skills/opengauss_commands/SKILL.md`.
  - SymPy CAS environment: `/home/goutev/.hermes/hermes-agent/venv/bin/python` contains `sympy 1.14.0`.
  - Process table check: Active background Lake build in progress on canonical modules; sequential build lock must be maintained.
  - Prior sandboxes: `.agents/sandbox_surgical_o1/` and `.agents/sandbox_weak_drazin_o1/` established the standard layout (`CAS/`, `lean/`, `diffs/`, `audit/`).

---

## 2. Logic Chain

1. **Root Cause of Compiler Overhead**:
   - The file currently imports `Mathlib.Tactic`, incurring global tactic initialization and dependency graph loading.
   - In `causal_antisymm`, executing `simp` over 25 case splits forces 25 runs of the simplifier engine, emitting bloated proof terms.
   - In `canonical_chain`, `norm_num` elaborates an arithmetic proof tree when the goal is a sequence of successor inequalities.
   - In `projector_pair_bilinear_scale`, invoking `ring` is redundant because Mathlib already provides `mul_mul_mul_comm`.

2. **OpenGauss `/golf` and `/refactor` Synthesis**:
   - **Prune Heavy Imports**: Remove `import Mathlib.Tactic`. Retain only `import Mathlib.Data.Real.Basic`. All required ring and order lemmas exist in `Mathlib.Data.Real.Basic`.
   - **$O(1)$ Poset Antisymmetry via Kernel Discrimination**:
     - `causallyPrecedes a b` is defined as `rank a ≤ rank b`.
     - `Nat.le_antisymm hab hba` proves `rank a = rank b`.
     - We introduce the focused helper lemma:
       ```lean
       theorem rank_inj : ∀ {a b : Archetype}, rank a = rank b → a = b := by
         intro a b h
         cases a <;> cases b <;> first | rfl | contradiction
       ```
       Here, the 5 diagonal goals close by `rfl` ($O(1)$ syntactic identity), while the 20 off-diagonal goals provide hypotheses like $195 = 196$, which `contradiction` refutes in $O(1)$ kernel time via `Nat.noConfusion`.
     - `causal_antisymm` then becomes an immediate single-term application:
       ```lean
       theorem causal_antisymm {a b : Archetype} (hab : causallyPrecedes a b) (hba : causallyPrecedes b a) : a = b :=
         rank_inj (Nat.le_antisymm hab hba)
       ```
   - **Pure Term Witness for `canonical_chain`**:
     - Each step is $n \le n + 1$, which is definitionally witnessed by `Nat.le_succ n`.
     - Hence:
       ```lean
       theorem canonical_chain :
           causallyPrecedes .fieldCorrelator .detectorProjector ∧
           causallyPrecedes .detectorProjector .modeNullspace ∧
           causallyPrecedes .modeNullspace .rankHierarchy ∧
           causallyPrecedes .rankHierarchy .scaleInvariantObservable :=
         ⟨Nat.le_succ 195, Nat.le_succ 196, Nat.le_succ 197, Nat.le_succ 198⟩
       ```
     - Zero tactics, instantaneous kernel checking.
   - **Term Proof for `projector_pair_bilinear_scale`**:
     - `mul_mul_mul_comm ε₁ ε₂ a b` directly closes `(ε₁ * ε₂) * (a * b) = (ε₁ * a) * (ε₂ * b)` in $O(1)$ steps.
   - **Targeted Rewrites for `modeTrace` & Linearity**:
     - `oscillatory_modes_annihilated`: `dsimp [modeTrace]; rw [MulZeroClass.zero_mul, AddMonoid.add_zero]`.
     - `modeTrace_linear`: `dsimp [modeTrace]; repeat rw [MulZeroClass.zero_mul, AddMonoid.add_zero]`.
     - `projector_single_linear`: `dsimp [projectSingle]; rw [mul_add, mul_left_comm detector.singleEfficiency r₁, mul_left_comm detector.singleEfficiency r₂]`.
   - **Deduplication**:
     - `detector_projection_parabola` reuses `coincidence_is_rank_two`.

3. **SymPy CAS Mathematical Certificate Strategy**:
   - A dedicated Python script `cas_field_correlator_certificate.py` mathematically validates the underlying geometric structures:
     - **Detector Projector**: Verifies exact matrix linearity $D(r_1 F_1 + r_2 F_2) = r_1 D(F_1) + r_2 D(F_2)$ and tensor scaling $(D_1 \otimes D_2)(F_1 \otimes F_2) = (D_1 F_1) \otimes (D_2 F_2)$.
     - **Mode Nullspace Projection**: Verifies idempotence ($\Pi_0^2 = \Pi_0, \Pi_1^2 = \Pi_1$), orthogonality ($\Pi_0 \Pi_1 = 0$), completeness ($\Pi_0 + \Pi_1 = I_2$), and annihilation ($T \Pi_1 = 0$).
     - **Rank Hierarchy**: Verifies degree-1 singles $S(X) = (N_0 \varepsilon) X$, degree-2 coincidences $C(X) = (N_0 K) X^2$, and the parabolic coordinate identity $C(X) - (N_0 K) X^2 \equiv 0$.
     - **Causal Poset Chain**: Validates rank array $[195, 196, 197, 198, 199]$, checking strict monotonicity $\Delta = 1$, injectivity, and reflexivity/antisymmetry/transitivity.
   - Emits `certificate.json` containing exact verified constants, matrix representations, and proof terms.

4. **Subagent Sandbox Isolation**:
   - All Phase 1 work must be performed strictly inside `.agents/sandbox_correlator/`.
   - Live file `lean/InfoGeometry/Detector/FieldCorrelatorProjection.lean` remains untouched until Gate Panel approval in Milestone 12.

---

## 3. Caveats

- The global build is currently compiling other targets (`QuasilatticeWaveMechanicsBridge`, `SignedParticleBridge`, etc.). Lake commands should only be run sequentially via `tools/infra/run_locked_lake_build.py` or when compiler processes are idle.
- Python CAS scripts requiring `sympy` must use `/home/goutev/.hermes/hermes-agent/venv/bin/python` because the system default python environment lacks `sympy`.
- No modifications were made to live repository source files during this Phase 0 exploration.

---

## 4. Conclusion

The compression of `lean/InfoGeometry/Detector/FieldCorrelatorProjection.lean` is completely solvable with $O(1)$ efficiency:
1. Eliminates `import Mathlib.Tactic`, removing massive transitive elaboration overhead.
2. Eliminates 25-case `simp` in `causal_antisymm` via `rank_inj` and `Nat.le_antisymm`.
3. Eliminates `norm_num` in `canonical_chain` via 4-tuple of `Nat.le_succ`.
4. Eliminates `by ring` in `projector_pair_bilinear_scale` via `mul_mul_mul_comm`.
5. Deduplicates `detector_projection_parabola`.
6. Attaches a SymPy CAS certificate validating all detector projection and poset invariants.

### Proposed Refactored Lean Module (`FieldCorrelatorProjection.lean`):
```lean
import Mathlib.Data.Real.Basic

namespace DetectorGeometry.FieldCorrelatorProjection

section FieldCorrelator

structure FieldCorrelator where
  singleAmplitude : ℝ
  pairAmplitude : ℝ

structure DetectorProjector where
  singleEfficiency : ℝ
  pairEfficiency : ℝ

def projectSingle (detector : DetectorProjector) (field : FieldCorrelator) : ℝ :=
  detector.singleEfficiency * field.singleAmplitude

def projectPair (detector : DetectorProjector) (field : FieldCorrelator) : ℝ :=
  detector.pairEfficiency * field.pairAmplitude

theorem projector_single_linear (detector : DetectorProjector)
    (field₁ field₂ : FieldCorrelator) (r₁ r₂ : ℝ) :
    projectSingle detector
        ⟨r₁ * field₁.singleAmplitude + r₂ * field₂.singleAmplitude,
          r₁ * field₁.pairAmplitude + r₂ * field₂.pairAmplitude⟩ =
      r₁ * projectSingle detector field₁ + r₂ * projectSingle detector field₂ := by
  dsimp [projectSingle]
  rw [mul_add, mul_left_comm detector.singleEfficiency r₁, mul_left_comm detector.singleEfficiency r₂]

theorem projector_pair_bilinear_scale (ε₁ ε₂ a b : ℝ) :
    (ε₁ * ε₂) * (a * b) = (ε₁ * a) * (ε₂ * b) :=
  mul_mul_mul_comm ε₁ ε₂ a b

end FieldCorrelator

section ModeProjection

def modeTrace (monopole oscillatory : ℝ) : ℝ := monopole + 0 * oscillatory

theorem oscillatory_modes_annihilated (monopole oscillatory : ℝ) :
    modeTrace monopole oscillatory = monopole := by
  dsimp [modeTrace]
  rw [MulZeroClass.zero_mul, AddMonoid.add_zero]

theorem modeTrace_linear (m₁ o₁ m₂ o₂ r₁ r₂ : ℝ) :
    modeTrace (r₁ * m₁ + r₂ * m₂) (r₁ * o₁ + r₂ * o₂) =
      r₁ * modeTrace m₁ o₁ + r₂ * modeTrace m₂ o₂ := by
  dsimp [modeTrace]
  repeat rw [MulZeroClass.zero_mul, AddMonoid.add_zero]

end ModeProjection

section RankHierarchy

def singlesCount (N₀ ε X : ℝ) : ℝ := N₀ * ε * X

def coincidenceCount (N₀ K X : ℝ) : ℝ := N₀ * K * X ^ 2

theorem coincidence_is_rank_two (N₀ K X : ℝ) :
    coincidenceCount N₀ K X = (N₀ * K) * X ^ 2 :=
  rfl

theorem square_root_coordinate_is_linear (N₀ ε X : ℝ) :
    singlesCount N₀ ε X = (N₀ * ε) * X :=
  rfl

theorem detector_projection_parabola (N₀ K X : ℝ) :
    coincidenceCount N₀ K X = (N₀ * K) * X ^ 2 :=
  coincidence_is_rank_two N₀ K X

end RankHierarchy

section CausalPoset

inductive Archetype
  | fieldCorrelator
  | detectorProjector
  | modeNullspace
  | rankHierarchy
  | scaleInvariantObservable
  deriving DecidableEq, Repr

def rank : Archetype → Nat
  | .fieldCorrelator => 195
  | .detectorProjector => 196
  | .modeNullspace => 197
  | .rankHierarchy => 198
  | .scaleInvariantObservable => 199

def causallyPrecedes (a b : Archetype) : Prop := rank a ≤ rank b

theorem causal_refl (a : Archetype) : causallyPrecedes a a := le_rfl

theorem causal_trans {a b c : Archetype} :
    causallyPrecedes a b → causallyPrecedes b c → causallyPrecedes a c :=
  Nat.le_trans

theorem rank_inj : ∀ {a b : Archetype}, rank a = rank b → a = b := by
  intro a b h
  cases a <;> cases b <;> first | rfl | contradiction

theorem causal_antisymm {a b : Archetype} (hab : causallyPrecedes a b) (hba : causallyPrecedes b a) : a = b :=
  rank_inj (Nat.le_antisymm hab hba)

theorem canonical_chain :
    causallyPrecedes .fieldCorrelator .detectorProjector ∧
    causallyPrecedes .detectorProjector .modeNullspace ∧
    causallyPrecedes .modeNullspace .rankHierarchy ∧
    causallyPrecedes .rankHierarchy .scaleInvariantObservable :=
  ⟨Nat.le_succ 195, Nat.le_succ 196, Nat.le_succ 197, Nat.le_succ 198⟩

end CausalPoset

end DetectorGeometry.FieldCorrelatorProjection
```

---

## 5. Verification Method & Sandbox Specification

### Sandbox Layout (`.agents/sandbox_correlator/`)
```
.agents/sandbox_correlator/
├── CAS/
│   ├── cas_field_correlator_certificate.py    # SymPy certificate generator
│   └── certificate.json                       # Emitted deterministic CAS verification packet
├── lean/
│   └── InfoGeometry/
│       └── Detector/
│           └── FieldCorrelatorProjection.lean  # Surgical O(1) refactored Lean module
├── diffs/
│   └── field_correlator_projection.diff        # Unified diff against live repo file
├── audit/
│   ├── verification_report.md                 # Verification, metric & tactic elimination audit
│   └── proof_term_analysis.md                 # Heartbeat & kernel proof term inspection
└── scripts/
    └── verify_sandbox.sh                      # Locked compilation test script
```

### Verification Commands for Implementation Worker:
1. **CAS Certificate Run**:
   ```bash
   /home/goutev/.hermes/hermes-agent/venv/bin/python .agents/sandbox_correlator/CAS/cas_field_correlator_certificate.py
   ```
   Must exit with code 0 and emit `certificate.json`.
2. **Sandbox Compilation**:
   ```bash
   python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock
   lake env lean --threads 1 .agents/sandbox_correlator/lean/InfoGeometry/Detector/FieldCorrelatorProjection.lean
   ```
   Must compile cleanly with 0 warnings, 0 errors, 0 `sorry`, 0 `native_decide`, 0 `simpa using`.
3. **Diff Generation**:
   ```bash
   diff -u lean/InfoGeometry/Detector/FieldCorrelatorProjection.lean .agents/sandbox_correlator/lean/InfoGeometry/Detector/FieldCorrelatorProjection.lean > .agents/sandbox_correlator/diffs/field_correlator_projection.diff
   ```
4. **Invalidation Conditions**:
   - Any failure of `lake env lean` on the sandbox file.
   - Any use of `sorry` or `admit`.
   - Any introduction of `native_decide`.
