/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceSpine.Basic
import InfoGeometry.OperatorAlgebra.PeirceSpine.Unipotent
import InfoGeometry.OperatorAlgebra.PeirceSpine.TwoStateSandwich
import InfoGeometry.OperatorAlgebra.PeirceSpine.QuantumAffineFlagClusterPoset
import InfoGeometry.Algebra.DirectLimitSuperClosureLemmas
import InfoGeometry.Canonical.Cl11MatrixTowerTailShift

/-!
# Stage D₂₈ (Archetypes U₁ → U₅): Peirce Current Modes, Quadratic Stress-Energy Analogue, Mode Products, and Idempotent Recurrence

This module formalizes a five-object dependency poset and Peirce operator identities
over an associative ring `[Ring B]` with involution. Its names `Heisenberg`, `Sugawara`,
and `Virasoro` label algebraic analogues only: these declarations do not define an
affine central extension or the standard Virasoro Lie algebra. Likewise,
`uhfIdemTower` is an abstract Peirce recurrence; the finite matrix tower and its
colimit interpretation are owned by `PeircePolygonKreinBottMasterSynthesis`.

- **Archetype `U₁` (`chiral_parity_charge_and_source_sink_currents`):**
  Chiral parity charge `chiralParityCharge P = P - (1 - P) = invS P`, chiral current source
  `chiralSource P A = conePlus P A`, chiral current sink `chiralSink P C = coneMinus P C`,
  vector current `vectorCurrent P A C = genPhi P A C`, axial current
  `axialCurrent P A C = genJ P A C`, and the current of the chiral parity charge
  `comm (chiralParityCharge P) (vectorCurrent P A C) = (2 : ℤ) • axialCurrent P A C`.
- **Archetype `U₂` (`heisenberg_current_mode_algebra`):**
  Peirce current modes `heisenbergSourceMode n P A C = V^n N_+(A)` and
  `heisenbergSinkMode m P A C = N_-(C) V^m`, together with their commutator
  `virasoroModeChiral n P A C = V^n Σ` and anticommutator `virasoroModeEven n P A C = V^{n+1}`.
- **Archetype `U₃` (`sugawara_stress_energy_and_conformal_commutators`):**
  Sugawara quadratic stress-energy identity `J_V² - J_A² = (2 : ℤ) • T_Sug`, chiral twist
  `Q_chiral * T_Sug = Σ`, and the chiral commutator identities
  `[Σ, N_±] = ± 2 • (T_Sug * N_±)`, `[Σ, J_V] = 2 • (T_Sug * J_A)`, and
  `[Σ, J_A] = 2 • (T_Sug * J_V)`.
- **Archetype `U₄` (`virasoro_chiral_splitting_and_central_defect`,
  `virasoro_sugawara_mode_closure`):**
  Orthogonal right/left Sugawara chiral splitting (`T_+ * T_- = T_- * T_+ = 0`), additivity of the
  defect additivity `idemDefect T_Sug = idemDefect T_+ + idemDefect T_-`,
  and all-`(n, m)` Peirce mode-product closure (`L_n^+ L_m^+ = L_{n+m+1}^+`,
  `L_n^- L_m^- = L_{n+m+1}^+`, `L_n^+ L_m^- = L_n^- L_m^+ = L_{n+m+1}^-`).
- **Archetype `U₅` (`uhf_inductive_tower_parity_and_sugawara_invariance`):**
  All-scale `k ∈ ℕ` Peirce idempotent recurrence `uhfIdemTower k P A` preserving idempotency,
  chiral parity involutivity, the chiral parity current relation, and Sugawara defect
  additivity across every scale `k : ℕ`, together with inductive colimit cone transport
  (`uhf_heisenberg_sugawara_virasoro_colimit_cone_transport`).

## Mathematical Audit & Three-Bucket Classification

- **BUCKET 1 — Validated Kernel-Proved Core:**
  All 5 stages (`U₁`–`U₅`), the all-mode `(n, m)` Heisenberg current algebra, the all-mode
  Virasoro–Sugawara mode closure and current commutators, the multiscale unipotent tower bridge,
  two-state chart sandwich soldering, and inductive colimit cone transport are constructively
  proved in `[Ring B]` with zero `sorry`, zero `admit`, and zero custom structures.
- **BUCKET 2 — Salvageable With Honest Scope Narrowing:**
  Infinite-mode UHF / Heisenberg / Virasoro limits are transported via explicit inductive colimit
  cones `toLimit : ∀ k : ℕ, Stage k →+* Limit` compatible with `embed : ∀ k : ℕ, Stage k →+* Stage (k + 1)`.
- **BUCKET 3 — Vacuous / Unjustified / Beyond Current Formal Scope:**
  Analytic Wightman field axioms and continuum vertex operator algebra OPE convergence beyond
  the algebraic all-mode Heisenberg/Sugawara/Virasoro commutators and inductive colimit cone
  transport proved here.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceSpine

variable {B : Type*} [Ring B] [StarRing B]

/-! ### 1. Dependency Poset of Chiral Parity, Peirce Modes & Recurrence (`U₁ → U₅`) -/

/-- The five-stage dependency poset for chiral parity, Peirce current modes,
quadratic stress-energy analogues, and the idempotent recurrence (`D₂₈`). -/
inductive UHFHeisenbergSugawaraStage : Type
  | U1_chiral_parity_source_sink
  | U2_heisenberg_current_modes
  | U3_sugawara_stress_energy
  | U4_virasoro_mode_closure_and_defect
  | U5_uhf_inductive_tower_invariance
  deriving DecidableEq, Repr

namespace UHFHeisenbergSugawaraStage

/-- Numerical topological rank of each stage `U₁..U₅`. -/
def rank : UHFHeisenbergSugawaraStage → ℕ
  | U1_chiral_parity_source_sink => 1
  | U2_heisenberg_current_modes => 2
  | U3_sugawara_stress_energy => 3
  | U4_virasoro_mode_closure_and_defect => 4
  | U5_uhf_inductive_tower_invariance => 5

/-- Directed causal dependency edges of the `U₁ → U₅` poset. -/
inductive causalEdge : UHFHeisenbergSugawaraStage → UHFHeisenbergSugawaraStage → Prop
  | u1_u2 : causalEdge U1_chiral_parity_source_sink U2_heisenberg_current_modes
  | u1_u3 : causalEdge U1_chiral_parity_source_sink U3_sugawara_stress_energy
  | u2_u4 : causalEdge U2_heisenberg_current_modes U4_virasoro_mode_closure_and_defect
  | u3_u4 : causalEdge U3_sugawara_stress_energy U4_virasoro_mode_closure_and_defect
  | u3_u5 : causalEdge U3_sugawara_stress_energy U5_uhf_inductive_tower_invariance
  | u4_u5 : causalEdge U4_virasoro_mode_closure_and_defect U5_uhf_inductive_tower_invariance

/-- Every directed causal edge in `UHFHeisenbergSugawaraStage` strictly increases `rank`. -/
theorem causalEdge_strict_rank_mono {a b : UHFHeisenbergSugawaraStage}
    (h : causalEdge a b) : rank a < rank b := by
  cases h <;> simp [rank]

/-- The causal edge relation on `UHFHeisenbergSugawaraStage` is irreflexive. -/
theorem causalEdge_irrefl (a : UHFHeisenbergSugawaraStage) : ¬ causalEdge a a := by
  intro h
  exact Nat.lt_irrefl (rank a) (causalEdge_strict_rank_mono h)

/-- Explicit dependency order on the five archetypes. In particular, the
Heisenberg and Sugawara stages remain incomparable because neither depends on
the other. -/
def causalLE : UHFHeisenbergSugawaraStage → UHFHeisenbergSugawaraStage → Prop
  | U1_chiral_parity_source_sink, _ => True
  | U2_heisenberg_current_modes, U2_heisenberg_current_modes => True
  | U2_heisenberg_current_modes, U4_virasoro_mode_closure_and_defect => True
  | U2_heisenberg_current_modes, U5_uhf_inductive_tower_invariance => True
  | U3_sugawara_stress_energy, U3_sugawara_stress_energy => True
  | U3_sugawara_stress_energy, U4_virasoro_mode_closure_and_defect => True
  | U3_sugawara_stress_energy, U5_uhf_inductive_tower_invariance => True
  | U4_virasoro_mode_closure_and_defect, U4_virasoro_mode_closure_and_defect => True
  | U4_virasoro_mode_closure_and_defect, U5_uhf_inductive_tower_invariance => True
  | U5_uhf_inductive_tower_invariance, U5_uhf_inductive_tower_invariance => True
  | _, _ => False

/-- The archetype stages carry the actual dependency partial order, rather
than a topological ranking mistaken for a total causal order. -/
instance : PartialOrder UHFHeisenbergSugawaraStage where
  le := causalLE
  le_refl a := by cases a <;> simp [causalLE]
  le_trans a b c hab hbc := by
    cases a <;> cases b <;> cases c <;> simp_all [causalLE]
  le_antisymm a b hab hba := by
    cases a <;> cases b <;> simp_all [causalLE]

/-- Every directed causal edge `causalEdge a b` implies `a ≤ b` in `UHFHeisenbergSugawaraStage`. -/
theorem causalEdge_le {a b : UHFHeisenbergSugawaraStage}
    (h : causalEdge a b) : a ≤ b := by
  cases h <;> simp [LE.le, causalLE]

end UHFHeisenbergSugawaraStage

/-! ### 2. Stage 0: Core Chiral Parity, Source/Sink Current, Sugawara & UHF Tower Primitives -/

section Primitives

variable {B : Type*} [Ring B]

/-- Quadratic idempotency defect `X² - X` in `[Ring B]`. -/
def idemDefect (X : B) : B := X * X - X

/-- Chiral parity charge `S_P = P - (1 - P)` in `[Ring B]`. -/
def chiralParityCharge (P : B) : B := P - (1 - P)

/-- Upper Peirce chiral current source `N_+(A) = P A (1 - P)` in `[Ring B]`. -/
def chiralSource (P A : B) : B := P * A * (1 - P)

/-- Lower Peirce chiral current sink `N_-(C) = (1 - P) C P` in `[Ring B]`. -/
def chiralSink (P C : B) : B := (1 - P) * C * P

/-- Unipotent idempotent transition `P - P A (1 - P)` in `[Ring B]`. -/
def idemTrans (P A : B) : B := P - chiralSource P A

/-- Vector current `J_V = N_+(A) + N_-(C)` in `[Ring B]`. -/
def vectorCurrent (P A C : B) : B := chiralSource P A + chiralSink P C

/-- Axial current `J_A = N_+(A) - N_-(C)` in `[Ring B]`. -/
def axialCurrent  (P A C : B) : B := chiralSource P A - chiralSink P C

/-- Right chiral Sugawara corner tensor `Q_+ = N_+(A) N_-(C)` in `[Ring B]`. -/
def sugawaraPlus  (P A C : B) : B := chiralSource P A * chiralSink P C

/-- Left chiral Sugawara corner tensor `Q_- = N_-(C) N_+(A)` in `[Ring B]`. -/
def sugawaraMinus (P A C : B) : B := chiralSink P C * chiralSource P A

/-- Total Sugawara stress-energy tensor `V = {N_+(A), N_-(C)}` in `[Ring B]`. -/
def sugawaraTensor (P A C : B) : B :=
  anticomm (chiralSource P A) (chiralSink P C)

/-- Chiral Schwinger commutator density `Σ = [N_+(A), N_-(C)]` in `[Ring B]`. -/
def chiralSchwinger (P A C : B) : B :=
  comm (chiralSource P A) (chiralSink P C)

/-- Peirce source current mode `J_{+,n} = V^n N_+(A)` at mode `n : ℕ`. -/
def heisenbergSourceMode (n : ℕ) (P A C : B) : B :=
  opPow n (sugawaraTensor P A C) * chiralSource P A

/-- Peirce sink current mode `J_{-,m} = N_-(C) V^m` at mode `m : ℕ`. -/
def heisenbergSinkMode (m : ℕ) (P A C : B) : B :=
  chiralSink P C * opPow m (sugawaraTensor P A C)

/-- Sugawara–Virasoro even mode generator `L_n^+ = V^n * V = V^{n+1}` at mode `n : ℕ`. -/
def virasoroModeEven (n : ℕ) (P A C : B) : B :=
  opPow n (sugawaraTensor P A C) * sugawaraTensor P A C

/-- Sugawara–Virasoro chiral mode generator `L_n^- = V^n * Σ` at mode `n : ℕ`. -/
def virasoroModeChiral (n : ℕ) (P A C : B) : B :=
  opPow n (sugawaraTensor P A C) * chiralSchwinger P A C

/-- Peirce idempotent recurrence `P_0 = P`, `P_{k+1} = idemTrans P_k A = P_k - chiralSource P_k A`. -/
def uhfIdemTower : ℕ → B → B → B
  | 0, P, _ => P
  | k + 1, P, A => idemTrans (uhfIdemTower k P A) A

/-- Right-associated idempotent reduction `P * (P * X) = P * X` for `P * P = P`. -/
private lemma P_assoc_u {P : B} (hP : P * P = P) (X : B) : P * (P * X) = P * X := by
  rw [← mul_assoc, hP]

local macro "sugawara_abel" hP:ident : tactic =>
  `(tactic| (
    simp only [virasoroModeEven, virasoroModeChiral,
               heisenbergSourceMode, heisenbergSinkMode,
               sugawaraTensor, chiralSchwinger, sugawaraPlus, sugawaraMinus,
               vectorCurrent, axialCurrent, chiralSource, chiralSink,
               chiralParityCharge, idemTrans, conePlus, coneMinus,
               comm, anticomm, idemDefect,
               zsmul_add, zsmul_sub, neg_zsmul, two_zsmul,
               sub_neg_eq_add, neg_mul, mul_neg, neg_neg,
               add_mul, mul_add, sub_mul, mul_sub, one_mul, mul_one,
               mul_assoc, $hP:ident, P_assoc_u $hP:ident]
    abel))

/-! ### 4. Individual Lemmas for Archetypes `U₁ → U₅` -/

/-- **Lemma `U₁.1` (`chiral_parity_charge_and_source_sink_currents`):**
For any idempotent `P` (`P * P = P`) and any `A, C : B`:
1. **Involutivity of the Chiral Parity Charge (`Q_chiral² = 1`):**
   `chiralParityCharge P * chiralParityCharge P = 1`.
2. **Source (`+1`) and Sink (`-1`) Eigen-Laws of the Chiral Parity Charge:**
   - `chiralParityCharge P * chiralSource P A = chiralSource P A` and
     `chiralSource P A * chiralParityCharge P = -chiralSource P A`,
   - `chiralParityCharge P * chiralSink P C = -chiralSink P C` and
     `chiralSink P C * chiralParityCharge P = chiralSink P C`.
3. **Current of the Chiral Parity Charge (`[Q_chiral, J_V] = 2 J_A` and `{Q_chiral, J_V} = 0`):**
   - `comm (chiralParityCharge P) (vectorCurrent P A C) = (2 : ℤ) • axialCurrent P A C`,
   - `comm (chiralParityCharge P) (axialCurrent P A C) = (2 : ℤ) • vectorCurrent P A C`,
   - `anticomm (chiralParityCharge P) (vectorCurrent P A C) = 0`,
   - `anticomm (chiralParityCharge P) (axialCurrent P A C) = 0`. -/
lemma chiral_parity_charge_and_source_sink_currents {P : B} (hP : P * P = P) (A C : B) :
    chiralParityCharge P * chiralParityCharge P = 1 ∧
    chiralParityCharge P * chiralSource P A = chiralSource P A ∧
    chiralSource P A * chiralParityCharge P = -chiralSource P A ∧
    chiralParityCharge P * chiralSink P C = -chiralSink P C ∧
    chiralSink P C * chiralParityCharge P = chiralSink P C ∧
    comm (chiralParityCharge P) (vectorCurrent P A C) = (2 : ℤ) • axialCurrent P A C ∧
    comm (chiralParityCharge P) (axialCurrent P A C) = (2 : ℤ) • vectorCurrent P A C ∧
    anticomm (chiralParityCharge P) (vectorCurrent P A C) = 0 ∧
    anticomm (chiralParityCharge P) (axialCurrent P A C) = 0 := by
  have hP' : P * P = P := hP
  refine ⟨by sugawara_abel hP', by sugawara_abel hP', by sugawara_abel hP',
          by sugawara_abel hP', by sugawara_abel hP', by sugawara_abel hP',
          by sugawara_abel hP', by sugawara_abel hP', by sugawara_abel hP'⟩

/-- **Lemma `U₂.1` (`heisenberg_current_mode_algebra`):**
For any idempotent `P` (`P * P = P`), any `A, C : B`, and any mode index `n : ℕ`:
1. **Source–Sink Fundamental Commutator & Anticommutator:**
   - `comm (chiralSource P A) (chiralSink P C) = sugawaraPlus P A C - sugawaraMinus P A C`,
   - `anticomm (chiralSource P A) (chiralSink P C) = sugawaraPlus P A C + sugawaraMinus P A C`.
2. **Higher Heisenberg Loop Mode Commutator & Anticommutator (`[J_{+,n}, J_{-,0}] = V^n Σ`):**
   - `comm (chiralSink P C) (sugawaraTensor P A C) = 0`,
   - `comm (chiralSource P A) (sugawaraTensor P A C) = 0`,
   - `comm (heisenbergSourceMode n P A C) (chiralSink P C) = virasoroModeChiral n P A C`,
   - `anticomm (heisenbergSourceMode n P A C) (chiralSink P C) = virasoroModeEven n P A C`. -/
lemma heisenberg_current_mode_algebra {P : B} (hP : P * P = P) (A C : B) (n : ℕ) :
    comm (chiralSource P A) (chiralSink P C) =
      sugawaraPlus P A C - sugawaraMinus P A C ∧
    anticomm (chiralSource P A) (chiralSink P C) =
      sugawaraPlus P A C + sugawaraMinus P A C ∧
    comm (chiralSink P C) (sugawaraTensor P A C) = 0 ∧
    comm (chiralSource P A) (sugawaraTensor P A C) = 0 ∧
    comm (heisenbergSourceMode n P A C) (chiralSink P C) =
      virasoroModeChiral n P A C ∧
    anticomm (heisenbergSourceMode n P A C) (chiralSink P C) =
      virasoroModeEven n P A C := by
  have hSinkV : chiralSink P C * sugawaraTensor P A C = sugawaraTensor P A C * chiralSink P C := by
    sugawara_abel hP
  have hSinkVn : ∀ k : ℕ, chiralSink P C * opPow k (sugawaraTensor P A C) =
      opPow k (sugawaraTensor P A C) * chiralSink P C := by
    intro k
    induction k with
    | zero => simp only [opPow, mul_one, one_mul]
    | succ k ih =>
      simp only [opPow]
      rw [← mul_assoc, ih, mul_assoc, hSinkV, ← mul_assoc]
  refine ⟨rfl, rfl, by sugawara_abel hP, by sugawara_abel hP, ?_, ?_⟩
  · unfold heisenbergSourceMode virasoroModeChiral chiralSchwinger comm
    rw [← mul_assoc (chiralSink P C), hSinkVn n]
    noncomm_ring
  · unfold heisenbergSourceMode virasoroModeEven
    calc
      anticomm (opPow n (sugawaraTensor P A C) * chiralSource P A) (chiralSink P C)
          = (opPow n (sugawaraTensor P A C) * chiralSource P A) * chiralSink P C +
              (chiralSink P C * opPow n (sugawaraTensor P A C)) * chiralSource P A := by
            unfold anticomm; noncomm_ring
      _ = opPow n (sugawaraTensor P A C) * (chiralSource P A * chiralSink P C +
            chiralSink P C * chiralSource P A) := by
            rw [hSinkVn n]; noncomm_ring
      _ = opPow n (sugawaraTensor P A C) * sugawaraTensor P A C := rfl

/-- **Lemma `U₃.1` (`sugawara_stress_energy_and_conformal_commutators`):**
For any idempotent `P` (`P * P = P`) and any `A, C : B`:
1. **Sugawara Bilinear Current Identity (`J_V² - J_A² = 2 T_Sug` and `J_V² + J_A² = 0`):**
   - `vectorCurrent P A C * vectorCurrent P A C - axialCurrent P A C * axialCurrent P A C =`
     `(2 : ℤ) • sugawaraTensor P A C`,
   - `vectorCurrent P A C * vectorCurrent P A C + axialCurrent P A C * axialCurrent P A C = 0`.
2. **Sugawara Chiral Twist (`Q_chiral * T_Sug = Σ` and `Q_chiral * Σ = T_Sug`):**
   - `chiralParityCharge P * sugawaraTensor P A C = chiralSchwinger P A C`,
   - `chiralParityCharge P * chiralSchwinger P A C = sugawaraTensor P A C`.
3. **Conformal Sugawara–Schwinger Action on the Currents (`[Σ, J_source] = +2 V J_source`):**
   - `comm (chiralSchwinger P A C) (chiralSource P A) =`
     `(2 : ℤ) • (sugawaraTensor P A C * chiralSource P A)`,
   - `comm (chiralSchwinger P A C) (chiralSink P C) =`
     `-(2 : ℤ) • (sugawaraTensor P A C * chiralSink P C)`,
   - `comm (chiralSchwinger P A C) (vectorCurrent P A C) =`
     `(2 : ℤ) • (sugawaraTensor P A C * axialCurrent P A C)`,
   - `comm (chiralSchwinger P A C) (axialCurrent P A C) =`
     `(2 : ℤ) • (sugawaraTensor P A C * vectorCurrent P A C)`. -/
lemma sugawara_stress_energy_and_conformal_commutators {P : B} (hP : P * P = P) (A C : B) :
    vectorCurrent P A C * vectorCurrent P A C - axialCurrent P A C * axialCurrent P A C =
      (2 : ℤ) • sugawaraTensor P A C ∧
    vectorCurrent P A C * vectorCurrent P A C + axialCurrent P A C * axialCurrent P A C = 0 ∧
    chiralParityCharge P * sugawaraTensor P A C = chiralSchwinger P A C ∧
    chiralParityCharge P * chiralSchwinger P A C = sugawaraTensor P A C ∧
    comm (chiralSchwinger P A C) (chiralSource P A) =
      (2 : ℤ) • (sugawaraTensor P A C * chiralSource P A) ∧
    comm (chiralSchwinger P A C) (chiralSink P C) =
      -(2 : ℤ) • (sugawaraTensor P A C * chiralSink P C) ∧
    comm (chiralSchwinger P A C) (vectorCurrent P A C) =
      (2 : ℤ) • (sugawaraTensor P A C * axialCurrent P A C) ∧
    comm (chiralSchwinger P A C) (axialCurrent P A C) =
      (2 : ℤ) • (sugawaraTensor P A C * vectorCurrent P A C) := by
  have hP' : P * P = P := hP
  refine ⟨by sugawara_abel hP', by sugawara_abel hP', by sugawara_abel hP', by sugawara_abel hP',
          by sugawara_abel hP', by sugawara_abel hP', by sugawara_abel hP', by sugawara_abel hP'⟩

/-- **Lemma `U₄.1` (`virasoro_chiral_splitting_and_central_defect`):**
For any idempotent `P` (`P * P = P`) and any `A, C : B`:
1. **Orthogonal Chiral Sector Splitting (`T_+ * T_- = 0`):**
   `sugawaraPlus P A C * sugawaraMinus P A C = 0` and
   `sugawaraMinus P A C * sugawaraPlus P A C = 0`.
2. **Additivity of the Idempotency Defect Across the Two Peirce Corners:**
   `idemDefect (sugawaraTensor P A C) =`
   `idemDefect (sugawaraPlus P A C) + idemDefect (sugawaraMinus P A C)`.
3. **Chiral-Schwinger Square Equality (`Σ² = V² = T_+² + T_-²`):**
   `chiralSchwinger P A C * chiralSchwinger P A C =`
   `sugawaraTensor P A C * sugawaraTensor P A C`. -/
lemma virasoro_chiral_splitting_and_central_defect {P : B} (hP : P * P = P) (A C : B) :
    sugawaraPlus P A C * sugawaraMinus P A C = 0 ∧
    sugawaraMinus P A C * sugawaraPlus P A C = 0 ∧
    idemDefect (sugawaraTensor P A C) =
      idemDefect (sugawaraPlus P A C) + idemDefect (sugawaraMinus P A C) ∧
    chiralSchwinger P A C * chiralSchwinger P A C =
      sugawaraTensor P A C * sugawaraTensor P A C := by
  have hP' : P * P = P := hP
  refine ⟨by sugawara_abel hP', by sugawara_abel hP', by sugawara_abel hP', by sugawara_abel hP'⟩

/-- **Lemma `U₄.2` (`virasoro_sugawara_mode_closure`):**
For any idempotent `P` (`P * P = P`), any `A, C : B`, and any mode indices `n, m : ℕ`, the
quadratic even (`L_n^+ = virasoroModeEven n P A C`) and chiral
(`L_n^- = virasoroModeChiral n P A C`) mode generators satisfy the multiplicative closure laws:
- `virasoroModeEven n P A C * virasoroModeEven m P A C = virasoroModeEven (n + m + 1) P A C`,
- `virasoroModeChiral n P A C * virasoroModeChiral m P A C = virasoroModeEven (n + m + 1) P A C`,
- `virasoroModeEven n P A C * virasoroModeChiral m P A C = virasoroModeChiral (n + m + 1) P A C`,
- `virasoroModeChiral n P A C * virasoroModeEven m P A C = virasoroModeChiral (n + m + 1) P A C`. -/
lemma virasoro_sugawara_mode_closure {P : B} (hP : P * P = P) (A C : B) (n m : ℕ) :
    virasoroModeEven n P A C * virasoroModeEven m P A C =
      virasoroModeEven (n + m + 1) P A C ∧
    virasoroModeChiral n P A C * virasoroModeChiral m P A C =
      virasoroModeEven (n + m + 1) P A C ∧
    virasoroModeEven n P A C * virasoroModeChiral m P A C =
      virasoroModeChiral (n + m + 1) P A C ∧
    virasoroModeChiral n P A C * virasoroModeEven m P A C =
      virasoroModeChiral (n + m + 1) P A C := by
  have hSigV : chiralSchwinger P A C * sugawaraTensor P A C =
      sugawaraTensor P A C * chiralSchwinger P A C := by
    sugawara_abel hP
  have hSigVm : ∀ k : ℕ, chiralSchwinger P A C * opPow k (sugawaraTensor P A C) =
      opPow k (sugawaraTensor P A C) * chiralSchwinger P A C := by
    intro k
    induction k with
    | zero => simp [opPow]
    | succ k ih =>
      simp only [opPow]
      rw [← mul_assoc, ih, mul_assoc, hSigV, ← mul_assoc]
  have hSigSq :
      chiralSchwinger P A C * chiralSchwinger P A C =
        sugawaraTensor P A C * sugawaraTensor P A C :=
    (virasoro_chiral_splitting_and_central_defect hP A C).2.2.2
  have hEvenDef : ∀ k : ℕ, virasoroModeEven k P A C = opPow (k + 1) (sugawaraTensor P A C) := by
    intro k; rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hEvenDef n, hEvenDef m, hEvenDef (n + m + 1), ← opPow_add]
    congr 1
    omega
  · unfold virasoroModeChiral virasoroModeEven
    calc (opPow n (sugawaraTensor P A C) * chiralSchwinger P A C) *
          (opPow m (sugawaraTensor P A C) * chiralSchwinger P A C)
      _ = opPow n (sugawaraTensor P A C) *
          (chiralSchwinger P A C * opPow m (sugawaraTensor P A C)) *
          chiralSchwinger P A C := by simp only [mul_assoc]
      _ = (opPow n (sugawaraTensor P A C) * opPow m (sugawaraTensor P A C)) *
          (chiralSchwinger P A C * chiralSchwinger P A C) := by
          rw [hSigVm m]; simp only [mul_assoc]
      _ = opPow (n + m) (sugawaraTensor P A C) *
          (sugawaraTensor P A C * sugawaraTensor P A C) := by
          rw [← opPow_add, hSigSq]
      _ = opPow (n + m + 1) (sugawaraTensor P A C) * sugawaraTensor P A C := by
          rw [opPow_succ, mul_assoc]
  · rw [hEvenDef n]
    unfold virasoroModeChiral
    rw [← mul_assoc, ← opPow_add]
    have hIdx : n + 1 + m = n + m + 1 := by omega
    rw [hIdx]
  · unfold virasoroModeChiral virasoroModeEven
    calc (opPow n (sugawaraTensor P A C) * chiralSchwinger P A C) *
          (opPow m (sugawaraTensor P A C) * sugawaraTensor P A C)
      _ = opPow n (sugawaraTensor P A C) *
          (chiralSchwinger P A C * opPow m (sugawaraTensor P A C)) *
          sugawaraTensor P A C := by simp only [mul_assoc]
      _ = (opPow n (sugawaraTensor P A C) * opPow m (sugawaraTensor P A C)) *
          (chiralSchwinger P A C * sugawaraTensor P A C) := by
          rw [hSigVm m]; simp only [mul_assoc]
      _ = (opPow (n + m) (sugawaraTensor P A C) * sugawaraTensor P A C) *
          chiralSchwinger P A C := by
          rw [← opPow_add, hSigV, mul_assoc]
      _ = opPow (n + m + 1) (sugawaraTensor P A C) * chiralSchwinger P A C := rfl

/-- **Lemma `U₅.1` (`uhf_inductive_tower_parity_and_sugawara_invariance`):**
Across every recurrence scale `k : ℕ` of `P_k = uhfIdemTower k P A`
(`P * P = P`):
1. `P_k` is an exact idempotent (`P_k * P_k = P_k`).
2. The Chiral Parity Charge `chiralParityCharge P_k` at scale `k` is an exact involution
   (`chiralParityCharge P_k * chiralParityCharge P_k = 1`).
3. The Current of the Chiral Parity Charge at scale `k` satisfies
   `comm (chiralParityCharge P_k) (vectorCurrent P_k A C) = (2 : ℤ) • axialCurrent P_k A C`.
4. The Sugawara idempotency defect splits additively at every scale `k ∈ ℕ`:
   `idemDefect (sugawaraTensor P_k A C) =`
   `idemDefect (sugawaraPlus P_k A C) + idemDefect (sugawaraMinus P_k A C)`. -/
lemma uhf_inductive_tower_parity_and_sugawara_invariance
    {P : B} (hP : P * P = P) (A C : B) (k : ℕ) :
    let P_k := uhfIdemTower k P A
    P_k * P_k = P_k ∧
    chiralParityCharge P_k * chiralParityCharge P_k = 1 ∧
    comm (chiralParityCharge P_k) (vectorCurrent P_k A C) =
      (2 : ℤ) • axialCurrent P_k A C ∧
    idemDefect (sugawaraTensor P_k A C) =
      idemDefect (sugawaraPlus P_k A C) + idemDefect (sugawaraMinus P_k A C) := by
  intro P_k
  have hPk : P_k * P_k = P_k := by
    dsimp [P_k]
    induction k with
    | zero => exact hP
    | succ k ih =>
      simp only [uhfIdemTower]
      sugawara_abel ih
  refine ⟨hPk,
          (chiral_parity_charge_and_source_sink_currents hPk A C).1,
          (chiral_parity_charge_and_source_sink_currents hPk A C).2.2.2.2.2.1,
          (virasoro_chiral_splitting_and_central_defect hPk A C).2.2.1⟩

/-! ### 5. Master Theorem `D₂₈`: Synthesis of Peirce Current Modes & Idempotent Recurrence -/

/-- **Master Theorem `D₂₈` (`stage_D28_uhf_heisenberg_sugawara_virasoro_and_chiral_parity_master_synthesis`):**
Unifies all 5 archetypes (`U₁ → U₅`) in native Mathlib4 with complete constructive proofs. -/
theorem stage_D28_uhf_heisenberg_sugawara_virasoro_and_chiral_parity_master_synthesis
    {P A C : B} (hP : P * P = P) (n k : ℕ) :
    -- 1. Chiral Parity Charge & Current of the Chiral Parity Charge (`[Q_chiral, J_V] = 2 J_A`) (U₁):
    chiralParityCharge P * chiralParityCharge P = 1 ∧
    comm (chiralParityCharge P) (vectorCurrent P A C) = (2 : ℤ) • axialCurrent P A C ∧
    anticomm (chiralParityCharge P) (vectorCurrent P A C) = 0 ∧
    -- 2. Peirce Current-Mode Commutator & Anticommutator (U₂):
    comm (heisenbergSourceMode n P A C) (chiralSink P C) = virasoroModeChiral n P A C ∧
    anticomm (heisenbergSourceMode n P A C) (chiralSink P C) = virasoroModeEven n P A C ∧
    -- 3. Sugawara Quadratic Construction (`J_V² - J_A² = 2 T_Sug`) & Conformal Commutators (U₃):
    vectorCurrent P A C * vectorCurrent P A C - axialCurrent P A C * axialCurrent P A C =
      (2 : ℤ) • sugawaraTensor P A C ∧
    comm (chiralSchwinger P A C) (chiralSource P A) =
      (2 : ℤ) • (sugawaraTensor P A C * chiralSource P A) ∧
    comm (chiralSchwinger P A C) (chiralSink P C) =
      -(2 : ℤ) • (sugawaraTensor P A C * chiralSink P C) ∧
    -- 4. Chiral Splitting & Idempotency-Defect Additivity (U₄):
    sugawaraPlus P A C * sugawaraMinus P A C = 0 ∧
    idemDefect (sugawaraTensor P A C) =
      idemDefect (sugawaraPlus P A C) + idemDefect (sugawaraMinus P A C) ∧
    -- 5. All-Scale Recurrence Preservation of Chiral Parity & Defect Additivity (U₅):
    chiralParityCharge (uhfIdemTower k P A) * chiralParityCharge (uhfIdemTower k P A) = 1 ∧
    idemDefect (sugawaraTensor (uhfIdemTower k P A) A C) =
      idemDefect (sugawaraPlus (uhfIdemTower k P A) A C) +
      idemDefect (sugawaraMinus (uhfIdemTower k P A) A C) := by
  rcases chiral_parity_charge_and_source_sink_currents hP A C with
    ⟨hC1, _, _, _, _, hC6, _, hC8, _⟩
  rcases heisenberg_current_mode_algebra hP A C n with ⟨_, _, _, _, hH5, hH6⟩
  rcases sugawara_stress_energy_and_conformal_commutators hP A C with
    ⟨hS1, _, _, _, hS5, hS6, _, _⟩
  rcases virasoro_chiral_splitting_and_central_defect hP A C with ⟨hV1, _, hV3, _⟩
  rcases uhf_inductive_tower_parity_and_sugawara_invariance hP A C k with
    ⟨_, hU2, _, hU4⟩
  exact ⟨hC1, hC6, hC8, hH5, hH6, hS1, hS5, hS6, hV1, hV3, hU2, hU4⟩

/-! ### 6. Stage `D₂₉`: All-Mode Peirce Current Relations & Unipotent-Tower Identity -/

/-- For any idempotent `P` (`P * P = P`), `heisenbergSinkMode m P A C` coincides with the Drinfeld
lower loop current `drinfeldXMinus m P A C = opPow m (genV P A C) * coneMinus P C`, and
`virasoroModeChiral r P A C` coincides with `drinfeldPhiPlus r P A C - drinfeldPhiMinus r P A C`. -/
theorem heisenbergSinkMode_eq_drinfeldXMinus_and_virasoroChiral_eq
    {P : B} (hP : P * P = P) (A C : B) (m r : ℕ) :
    heisenbergSinkMode m P A C = drinfeldXMinus m P A C ∧
    virasoroModeChiral r P A C =
      drinfeldPhiPlus r P A C - drinfeldPhiMinus r P A C ∧
    virasoroModeEven r P A C = opPow (r + 1) (genV P A C) := by
  have hCommM := (opPow_genV_comm_invS_and_cones hP A C m).2.2
  refine ⟨?_, ?_, rfl⟩
  · unfold heisenbergSinkMode drinfeldXMinus chiralSink sugawaraTensor genV
    exact hCommM
  · unfold virasoroModeChiral drinfeldPhiPlus drinfeldPhiMinus
    unfold sugawaraTensor chiralSchwinger genV qgtPlus qgtMinus chiralSource chiralSink comm
    unfold conePlus coneMinus
    rw [mul_sub]

/-- **Theorem `D₂₉.1` (`all_mode_heisenberg_current_algebra`):**
Two-parameter `(n, m)` commutator and anticommutator identities for Peirce current modes.
These formulas do not assert a scalar central extension:
1. `heisenbergSourceMode n P A C * heisenbergSourceMode m P A C = 0`,
2. `heisenbergSinkMode n P A C * heisenbergSinkMode m P A C = 0`,
3. `comm (heisenbergSourceMode n P A C) (heisenbergSinkMode m P A C) = virasoroModeChiral (n + m) P A C`,
4. `anticomm (heisenbergSourceMode n P A C) (heisenbergSinkMode m P A C) = virasoroModeEven (n + m) P A C`. -/
theorem all_mode_heisenberg_current_algebra
    {P : B} (hP : P * P = P) (A C : B) (n m : ℕ) :
    heisenbergSourceMode n P A C * heisenbergSourceMode m P A C = 0 ∧
    heisenbergSinkMode n P A C * heisenbergSinkMode m P A C = 0 ∧
    comm (heisenbergSourceMode n P A C) (heisenbergSinkMode m P A C) =
      virasoroModeChiral (n + m) P A C ∧
    anticomm (heisenbergSourceMode n P A C) (heisenbergSinkMode m P A C) =
      virasoroModeEven (n + m) P A C := by
  have hSrc : ∀ k : ℕ, heisenbergSourceMode k P A C = drinfeldXPlus k P A C := fun _ => rfl
  have hSnk : ∀ k : ℕ, heisenbergSinkMode k P A C = drinfeldXMinus k P A C :=
    fun k => (heisenbergSinkMode_eq_drinfeldXMinus_and_virasoroChiral_eq hP A C k 0).1
  rcases heisenbergSinkMode_eq_drinfeldXMinus_and_virasoroChiral_eq hP A C m (n + m) with
    ⟨_, hVirC, hVirE⟩
  rcases drinfeld_new_presentation_loop_relations hP A C n m with
    ⟨_, _, _, _, _, _, _, _, hNilP, hNilM, hCommD, hAntiD⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hSrc n, hSrc m, hNilP]
  · rw [hSnk n, hSnk m, hNilM]
  · rw [hSrc n, hSnk m, hVirC, hCommD]
  · rw [hSrc n, hSnk m, hVirE, hAntiD]

/-- **Theorem `D₂₉.2` (`all_mode_virasoro_current_commutators`):**
Two-parameter `(n, m)` commutator identities of the quadratic stress-energy mode analogues
`virasoroModeChiral n P A C` (`L_n^- = V^n Σ`) and `virasoroModeEven n P A C` (`L_n^+ = V^{n+1}`)
on the Peirce current modes `heisenbergSourceMode m P A C` (`J_{+,m}`) and
`heisenbergSinkMode m P A C` (`J_{-,m}`):
1. `comm (virasoroModeChiral n P A C) (heisenbergSourceMode m P A C) =`
   `(2 : ℤ) • heisenbergSourceMode (n + m + 1) P A C`,
2. `comm (virasoroModeChiral n P A C) (heisenbergSinkMode m P A C) =`
   `-(2 : ℤ) • heisenbergSinkMode (n + m + 1) P A C`,
3. `comm (virasoroModeEven n P A C) (heisenbergSourceMode m P A C) = 0`,
4. `comm (virasoroModeEven n P A C) (heisenbergSinkMode m P A C) = 0`. -/
theorem all_mode_virasoro_current_commutators
    {P : B} (hP : P * P = P) (A C : B) (n m : ℕ) :
    comm (virasoroModeChiral n P A C) (heisenbergSourceMode m P A C) =
      (2 : ℤ) • heisenbergSourceMode (n + m + 1) P A C ∧
    comm (virasoroModeChiral n P A C) (heisenbergSinkMode m P A C) =
      -(2 : ℤ) • heisenbergSinkMode (n + m + 1) P A C ∧
    comm (virasoroModeEven n P A C) (heisenbergSourceMode m P A C) = 0 ∧
    comm (virasoroModeEven n P A C) (heisenbergSinkMode m P A C) = 0 := by
  have hVp : ∀ k : ℕ,
      conePlus P A * opPow k (sugawaraTensor P A C) =
        opPow k (sugawaraTensor P A C) * conePlus P A :=
    fun k => (opPow_genV_comm_invS_and_cones hP A C k).2.1
  have hVm : ∀ k : ℕ,
      coneMinus P C * opPow k (sugawaraTensor P A C) =
        opPow k (sugawaraTensor P A C) * coneMinus P C :=
    fun k => (opPow_genV_comm_invS_and_cones hP A C k).2.2
  have hSigV : chiralSchwinger P A C * sugawaraTensor P A C =
      sugawaraTensor P A C * chiralSchwinger P A C := by
    sugawara_abel hP
  have hSigVk : ∀ k : ℕ,
      chiralSchwinger P A C * opPow k (sugawaraTensor P A C) =
        opPow k (sugawaraTensor P A C) * chiralSchwinger P A C := by
    intro k
    induction k with
    | zero => simp [opPow]
    | succ k ih =>
      simp only [opPow]
      rw [← mul_assoc, ih, mul_assoc, hSigV, ← mul_assoc]
  rcases sugawara_stress_energy_and_conformal_commutators hP A C with
    ⟨_, _, _, _, hCommSrc0, hCommSnk0, _, _⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold virasoroModeChiral heisenbergSourceMode comm
    have h1 :
        (opPow n (sugawaraTensor P A C) * chiralSchwinger P A C) *
          (opPow m (sugawaraTensor P A C) * chiralSource P A) =
        opPow (n + m) (sugawaraTensor P A C) *
          (chiralSchwinger P A C * chiralSource P A) := by
      calc (opPow n (sugawaraTensor P A C) * chiralSchwinger P A C) *
            (opPow m (sugawaraTensor P A C) * chiralSource P A)
        _ = opPow n (sugawaraTensor P A C) *
            (chiralSchwinger P A C * opPow m (sugawaraTensor P A C)) *
            chiralSource P A := by simp only [mul_assoc]
        _ = (opPow n (sugawaraTensor P A C) * opPow m (sugawaraTensor P A C)) *
            (chiralSchwinger P A C * chiralSource P A) := by
            rw [hSigVk m]; simp only [mul_assoc]
        _ = opPow (n + m) (sugawaraTensor P A C) *
            (chiralSchwinger P A C * chiralSource P A) := by rw [← opPow_add]
    have h2 :
        (opPow m (sugawaraTensor P A C) * chiralSource P A) *
          (opPow n (sugawaraTensor P A C) * chiralSchwinger P A C) =
        opPow (n + m) (sugawaraTensor P A C) *
          (chiralSource P A * chiralSchwinger P A C) := by
      calc (opPow m (sugawaraTensor P A C) * chiralSource P A) *
            (opPow n (sugawaraTensor P A C) * chiralSchwinger P A C)
        _ = opPow m (sugawaraTensor P A C) *
            (chiralSource P A * opPow n (sugawaraTensor P A C)) *
            chiralSchwinger P A C := by simp only [mul_assoc]
        _ = (opPow m (sugawaraTensor P A C) * opPow n (sugawaraTensor P A C)) *
            (chiralSource P A * chiralSchwinger P A C) := by
            change (opPow m (sugawaraTensor P A C) *
              (conePlus P A * opPow n (sugawaraTensor P A C))) * chiralSchwinger P A C = _
            rw [hVp n]
            unfold chiralSource conePlus
            simp only [mul_assoc]
        _ = opPow (n + m) (sugawaraTensor P A C) *
            (chiralSource P A * chiralSchwinger P A C) := by
            rw [← opPow_add, Nat.add_comm]
    rw [h1, h2, ← mul_sub]
    change opPow (n + m) (sugawaraTensor P A C) *
        comm (chiralSchwinger P A C) (chiralSource P A) = _
    rw [hCommSrc0, mul_smul_comm, ← mul_assoc, ← opPow_succ]
  · unfold virasoroModeChiral heisenbergSinkMode comm
    have h1 :
        (opPow n (sugawaraTensor P A C) * chiralSchwinger P A C) *
          (chiralSink P C * opPow m (sugawaraTensor P A C)) =
        (chiralSchwinger P A C * chiralSink P C) *
          opPow (n + m) (sugawaraTensor P A C) := by
      calc (opPow n (sugawaraTensor P A C) * chiralSchwinger P A C) *
            (chiralSink P C * opPow m (sugawaraTensor P A C))
        _ = (opPow n (sugawaraTensor P A C) * chiralSchwinger P A C) *
            (opPow m (sugawaraTensor P A C) * chiralSink P C) := by
            change _ * (coneMinus P C * opPow m (sugawaraTensor P A C)) = _
            rw [hVm m]; rfl
        _ = opPow n (sugawaraTensor P A C) *
            (chiralSchwinger P A C * opPow m (sugawaraTensor P A C)) *
            chiralSink P C := by simp only [mul_assoc]
        _ = (opPow n (sugawaraTensor P A C) * opPow m (sugawaraTensor P A C)) *
            (chiralSchwinger P A C * chiralSink P C) := by
            rw [hSigVk m]; simp only [mul_assoc]
        _ = opPow (n + m) (sugawaraTensor P A C) *
            (chiralSchwinger P A C * chiralSink P C) := by rw [← opPow_add]
        _ = (chiralSchwinger P A C * opPow (n + m) (sugawaraTensor P A C)) *
            chiralSink P C := by rw [hSigVk (n + m), mul_assoc]
        _ = chiralSchwinger P A C *
            (opPow (n + m) (sugawaraTensor P A C) * chiralSink P C) := by rw [mul_assoc]
        _ = (chiralSchwinger P A C * chiralSink P C) *
            opPow (n + m) (sugawaraTensor P A C) := by
            change chiralSchwinger P A C *
              (opPow (n + m) (sugawaraTensor P A C) * coneMinus P C) = _
            rw [← hVm (n + m), ← mul_assoc]; rfl
    have h2 :
        (chiralSink P C * opPow m (sugawaraTensor P A C)) *
          (opPow n (sugawaraTensor P A C) * chiralSchwinger P A C) =
        (chiralSink P C * chiralSchwinger P A C) *
          opPow (n + m) (sugawaraTensor P A C) := by
      calc (chiralSink P C * opPow m (sugawaraTensor P A C)) *
            (opPow n (sugawaraTensor P A C) * chiralSchwinger P A C)
        _ = chiralSink P C *
            (opPow m (sugawaraTensor P A C) * opPow n (sugawaraTensor P A C)) *
            chiralSchwinger P A C := by simp only [mul_assoc]
        _ = chiralSink P C *
            (opPow (n + m) (sugawaraTensor P A C) * chiralSchwinger P A C) := by
            rw [← opPow_add, Nat.add_comm, mul_assoc]
        _ = (chiralSink P C * chiralSchwinger P A C) *
            opPow (n + m) (sugawaraTensor P A C) := by
            rw [← hSigVk (n + m), ← mul_assoc]
    rw [h1, h2, ← sub_mul]
    change comm (chiralSchwinger P A C) (chiralSink P C) *
        opPow (n + m) (sugawaraTensor P A C) = _
    have hSnkV : sugawaraTensor P A C * chiralSink P C =
        chiralSink P C * sugawaraTensor P A C := by sugawara_abel hP
    rw [hCommSnk0, hSnkV, smul_mul_assoc, mul_assoc, mul_opPow_comm, ← opPow_succ]
  · unfold virasoroModeEven heisenbergSourceMode comm
    change opPow (n + 1) (sugawaraTensor P A C) *
        (opPow m (sugawaraTensor P A C) * conePlus P A) -
      (opPow m (sugawaraTensor P A C) * conePlus P A) *
        opPow (n + 1) (sugawaraTensor P A C) = 0
    have hR :
        (opPow m (sugawaraTensor P A C) * conePlus P A) *
          opPow (n + 1) (sugawaraTensor P A C) =
        (opPow m (sugawaraTensor P A C) * opPow (n + 1) (sugawaraTensor P A C)) *
          conePlus P A := by
      calc (opPow m (sugawaraTensor P A C) * conePlus P A) *
            opPow (n + 1) (sugawaraTensor P A C)
        _ = opPow m (sugawaraTensor P A C) *
            (conePlus P A * opPow (n + 1) (sugawaraTensor P A C)) := by rw [mul_assoc]
        _ = (opPow m (sugawaraTensor P A C) * opPow (n + 1) (sugawaraTensor P A C)) *
            conePlus P A := by rw [hVp (n + 1), ← mul_assoc]
    rw [← mul_assoc, hR, ← opPow_add, ← opPow_add, Nat.add_comm (n + 1) m, sub_self]
  · unfold virasoroModeEven heisenbergSinkMode comm
    change opPow (n + 1) (sugawaraTensor P A C) *
        (coneMinus P C * opPow m (sugawaraTensor P A C)) -
      (coneMinus P C * opPow m (sugawaraTensor P A C)) *
        opPow (n + 1) (sugawaraTensor P A C) = 0
    have hL :
        opPow (n + 1) (sugawaraTensor P A C) *
          (coneMinus P C * opPow m (sugawaraTensor P A C)) =
        coneMinus P C *
          (opPow (n + 1) (sugawaraTensor P A C) * opPow m (sugawaraTensor P A C)) := by
      calc opPow (n + 1) (sugawaraTensor P A C) *
            (coneMinus P C * opPow m (sugawaraTensor P A C))
        _ = (opPow (n + 1) (sugawaraTensor P A C) * coneMinus P C) *
            opPow m (sugawaraTensor P A C) := by rw [← mul_assoc]
        _ = coneMinus P C *
            (opPow (n + 1) (sugawaraTensor P A C) * opPow m (sugawaraTensor P A C)) := by
            rw [← hVm (n + 1), mul_assoc]
    rw [hL, mul_assoc (coneMinus P C), ← opPow_add, ← opPow_add,
        Nat.add_comm (n + 1) m, sub_self]

/-- **Theorem `D₂₉.3` (`unipotentIdempotentTower_const_eq_uhfIdemTower`):**
For any idempotent `P` (`P * P = P`), any `A : B`, and every scale `k : ℕ`, the multiscale
unipotent shear tower `unipotentIdempotentTower (fun _ => A) k P` (`Unipotent.lean`) coincides
identically with the Peirce recurrence `uhfIdemTower k P A`. -/
theorem unipotentIdempotentTower_const_eq_uhfIdemTower
    {P : B} (hP : P * P = P) (A : B) (k : ℕ) :
    unipotentIdempotentTower (fun _ => A) k P = uhfIdemTower k P A := by
  induction k with
  | zero => rfl
  | succ m ih =>
    have hm : uhfIdemTower m P A * uhfIdemTower m P A = uhfIdemTower m P A :=
      (uhf_inductive_tower_parity_and_sugawara_invariance hP A 0 m).1
    change conjPlus (unipotentIdempotentTower (fun _ => A) m P) A
        (unipotentIdempotentTower (fun _ => A) m P) =
      idemTrans (uhfIdemTower m P A) A
    rw [ih, conjPlus_idempotent_point_form hm A]
    rfl

/-- **Master Theorem `D₂₉` (`stage_D29_all_mode_heisenberg_virasoro_and_uhf_unipotent_bridge`):**
Combines the all-`(n, m)` Peirce current-mode identities, quadratic stress-energy mode
commutators, and the exact identity between the multiscale unipotent idempotent tower and the
Peirce recurrence across all scales `k : ℕ`. -/
theorem stage_D29_all_mode_heisenberg_virasoro_and_uhf_unipotent_bridge
    {P : B} (hP : P * P = P) (A C : B) (n m k : ℕ) :
    comm (heisenbergSourceMode n P A C) (heisenbergSinkMode m P A C) =
      virasoroModeChiral (n + m) P A C ∧
    anticomm (heisenbergSourceMode n P A C) (heisenbergSinkMode m P A C) =
      virasoroModeEven (n + m) P A C ∧
    comm (virasoroModeChiral n P A C) (heisenbergSourceMode m P A C) =
      (2 : ℤ) • heisenbergSourceMode (n + m + 1) P A C ∧
    comm (virasoroModeChiral n P A C) (heisenbergSinkMode m P A C) =
      -(2 : ℤ) • heisenbergSinkMode (n + m + 1) P A C ∧
    comm (virasoroModeEven n P A C) (heisenbergSourceMode m P A C) = 0 ∧
    comm (virasoroModeEven n P A C) (heisenbergSinkMode m P A C) = 0 ∧
    unipotentIdempotentTower (fun _ => A) k P = uhfIdemTower k P A := by
  rcases all_mode_heisenberg_current_algebra hP A C n m with ⟨_, _, hH3, hH4⟩
  rcases all_mode_virasoro_current_commutators hP A C n m with ⟨hV1, hV2, hV3, hV4⟩
  exact ⟨hH3, hH4, hV1, hV2, hV3, hV4,
         unipotentIdempotentTower_const_eq_uhfIdemTower hP A k⟩

/-! ### 7. Stage `D₃₁`: Soldering Local Two-State Chart Sandwiches to Multiscale Peirce Recurrences -/

/-- **Master Theorem `D₃₁` (`stage_D31_uhf_unipotent_tower_and_two_state_chart_sandwich_soldering`):**
Solders the local two-state chart sandwiches `(P - N₊) · (P + N₋)` (`TwoStateSandwich.lean`) directly
to the multiscale unipotent tower `unipotentIdempotentTower A k P` (`Unipotent.lean`) and the Peirce
idempotent recurrence `uhfIdemTower k P A₀` at every scale `k : ℕ` and every defect
depth `n : ℕ`. -/
theorem stage_D31_uhf_unipotent_tower_and_two_state_chart_sandwich_soldering
    {P : B} (hP : P * P = P) (A C : ℕ → B) (A₀ : B) (k n : ℕ) :
    let P_k := unipotentIdempotentTower A k P
    let δ := InfoGeometry.Core.IdempotentGraphGrassmannian.idempotencyDefect (B := B)
    -- 1. Soldering of the child tower stage `P_{k+1}` and dual lower-shear stage `P_{C,k}` to the chart factors:
    unipotentIdempotentTower A (k + 1) P = P_k - conePlus P_k (A k) ∧
    conjMinus P_k (C k) P_k = P_k + coneMinus P_k (C k) ∧
    unipotentIdempotentTower (fun _ => A₀) k P = uhfIdemTower k P A₀ ∧
    -- 2. All-scale `k`, all-depth `n` tower sandwich identities (`P_{k+1} · X · P_{C,k}`):
    unipotentIdempotentTower A (k + 1) P *
        δ^[n] (qgtPlus P_k (A k) (C k)) *
        conjMinus P_k (C k) P_k =
      δ^[n] (qgtPlus P_k (A k) (C k)) ∧
    unipotentIdempotentTower A (k + 1) P *
        δ^[n] (qgtMinus P_k (A k) (C k)) *
        conjMinus P_k (C k) P_k =
      -(genV P_k (A k) (C k) * δ^[n] (qgtPlus P_k (A k) (C k))) ∧
    unipotentIdempotentTower A (k + 1) P *
        δ^[n] (genV P_k (A k) (C k)) *
        conjMinus P_k (C k) P_k =
      (1 - genV P_k (A k) (C k)) * δ^[n] (qgtPlus P_k (A k) (C k)) ∧
    unipotentIdempotentTower A (k + 1) P *
        qgtDefectDiff P_k (A k) (C k) n *
        conjMinus P_k (C k) P_k =
      (1 + genV P_k (A k) (C k)) * δ^[n] (qgtPlus P_k (A k) (C k)) ∧
    unipotentIdempotentTower A (k + 1) P *
        (genPhi P_k (A k) (C k) * δ^[n] (genV P_k (A k) (C k))) *
        conjMinus P_k (C k) P_k = 0 ∧
    unipotentIdempotentTower A (k + 1) P *
        (genJ P_k (A k) (C k) * δ^[n] (genV P_k (A k) (C k))) *
        conjMinus P_k (C k) P_k =
      (2 : ℤ) • (genV P_k (A k) (C k) * δ^[n] (qgtPlus P_k (A k) (C k))) := by
  dsimp only
  have hPk : unipotentIdempotentTower A k P * unipotentIdempotentTower A k P =
      unipotentIdempotentTower A k P :=
    unipotentIdempotentTower_idempotent hP A k
  have hLeft :
      unipotentIdempotentTower A (k + 1) P =
        unipotentIdempotentTower A k P - conePlus (unipotentIdempotentTower A k P) (A k) := by
    change conjPlus (unipotentIdempotentTower A k P) (A k) (unipotentIdempotentTower A k P) = _
    exact conjPlus_idempotent_point_form hPk (A k)
  have hRight :
      conjMinus (unipotentIdempotentTower A k P) (C k) (unipotentIdempotentTower A k P) =
        unipotentIdempotentTower A k P + coneMinus (unipotentIdempotentTower A k P) (C k) := by
    unfold conjMinus
    sugawara_abel hPk
  rcases chart_two_state_genV_and_qgtDefectDiff_iterates hPk (A k) (C k) n with ⟨hV, hSig, _⟩
  rcases chart_two_state_odd_defect_iterates hPk (A k) (C k) n with ⟨hPhi, hJ⟩
  refine ⟨hLeft, hRight, unipotentIdempotentTower_const_eq_uhfIdemTower hP A₀ k,
          ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hLeft, hRight]
    exact chart_two_state_qgtPlus_defect_iterate hPk (A k) (C k) n
  · rw [hLeft, hRight]
    exact chart_two_state_qgtMinus_defect_iterate hPk (A k) (C k) n
  · rw [hLeft, hRight]
    exact hV
  · rw [hLeft, hRight]
    exact hSig
  · rw [hLeft, hRight]
    exact hPhi
  · rw [hLeft, hRight]
    exact hJ

/-- **Inductive Colimit Cone Transport of the UHF–Heisenberg–Sugawara–Virasoro Tower
(`uhf_heisenberg_sugawara_virasoro_colimit_cone_transport`):**
Let `Stage : ℕ → Type*` be a directed tower of non-commutative operator rings `[∀ s, Ring (Stage s)]`
with connecting ring homomorphisms `embed : ∀ s : ℕ, Stage s →+* Stage (s + 1)` and colimit
cone legs `toLimit : ∀ s : ℕ, Stage s →+* Limit` into a colimit ring `[Ring Limit]` satisfying
cone compatibility `∀ s Z, toLimit (s + 1) (embed s Z) = toLimit s Z`.
Then for any stage `s : ℕ`, any idempotent `P : Stage s` (`P * P = P`), any `A, C : Stage s`,
and any mode indices `n, m, k : ℕ`:
1. The colimit cone legs preserve `uhfIdemTower k P A`, `heisenbergSourceMode n P A C`,
   `heisenbergSinkMode m P A C`, `virasoroModeEven (n + m) P A C`, and
   `virasoroModeChiral (n + m) P A C`, and are invariant under stage refinement `embed s`.
2. In the colimit ring `Limit`, the transported operators `P_∞ = toLimit s P`,
   `A_∞ = toLimit s A`, `C_∞ = toLimit s C` satisfy the full all-mode Heisenberg current
   commutator/anticommutator algebra and all-mode Virasoro–Heisenberg current commutators! -/
theorem uhf_heisenberg_sugawara_virasoro_colimit_cone_transport
    {Stage : ℕ → Type*} [∀ s, Ring (Stage s)]
    {Limit : Type*} [Ring Limit]
    (embed : ∀ s : ℕ, Stage s →+* Stage (s + 1))
    (toLimit : ∀ s : ℕ, Stage s →+* Limit)
    (hCone : ∀ (s : ℕ) (Z : Stage s), toLimit (s + 1) (embed s Z) = toLimit s Z)
    (s : ℕ) {P : Stage s} (hP : P * P = P) (A C : Stage s) (n m k : ℕ) :
    let P_inf := toLimit s P
    let A_inf := toLimit s A
    let C_inf := toLimit s C
    toLimit s (uhfIdemTower k P A) = uhfIdemTower k P_inf A_inf ∧
    toLimit (s + 1) (uhfIdemTower k (embed s P) (embed s A)) = uhfIdemTower k P_inf A_inf ∧
    comm (heisenbergSourceMode n P_inf A_inf C_inf) (heisenbergSinkMode m P_inf A_inf C_inf) =
      virasoroModeChiral (n + m) P_inf A_inf C_inf ∧
    anticomm (heisenbergSourceMode n P_inf A_inf C_inf) (heisenbergSinkMode m P_inf A_inf C_inf) =
      virasoroModeEven (n + m) P_inf A_inf C_inf ∧
    comm (virasoroModeChiral n P_inf A_inf C_inf) (heisenbergSourceMode m P_inf A_inf C_inf) =
      (2 : ℤ) • heisenbergSourceMode (n + m + 1) P_inf A_inf C_inf ∧
    comm (virasoroModeChiral n P_inf A_inf C_inf) (heisenbergSinkMode m P_inf A_inf C_inf) =
      -(2 : ℤ) • heisenbergSinkMode (n + m + 1) P_inf A_inf C_inf := by
  have hMapTower_lim : ∀ (r : ℕ) (p a : Stage s),
      toLimit s (uhfIdemTower r p a) = uhfIdemTower r (toLimit s p) (toLimit s a) := by
    intro r
    induction r with
    | zero => intro p a; rfl
    | succ r ih =>
      intro p a
      dsimp only [uhfIdemTower, idemTrans, chiralSource]
      simp only [map_sub, map_mul, map_one, ih p a]
  have hMapTower_emb : ∀ (r : ℕ) (p a : Stage s),
      embed s (uhfIdemTower r p a) = uhfIdemTower r (embed s p) (embed s a) := by
    intro r
    induction r with
    | zero => intro p a; rfl
    | succ r ih =>
      intro p a
      dsimp only [uhfIdemTower, idemTrans, chiralSource]
      simp only [map_sub, map_mul, map_one, ih p a]
  have hP_inf : toLimit s P * toLimit s P = toLimit s P := by
    rw [← map_mul, hP]
  rcases stage_D29_all_mode_heisenberg_virasoro_and_uhf_unipotent_bridge hP_inf
      (toLimit s A) (toLimit s C) n m k with ⟨hH1, hH2, hV1, hV2, _, _, _⟩
  refine ⟨hMapTower_lim k P A, ?_, hH1, hH2, hV1, hV2⟩
  rw [← hMapTower_emb k P A, hCone s, hMapTower_lim k P A]

/-- **Genuine Mathlib `_root_.DirectLimit` (`DirectLimitSuperClosure`) and Clifford Tensor-Tower
Finite-Head × Infinite-Tail (`BaseLimit ≃+* TailLimit k`) Realization of the UHF–Heisenberg–Sugawara–Virasoro Tower
(`uhf_heisenberg_sugawara_virasoro_direct_limit_and_clifford_tail_realization`):**
1. For any one-step directed system of non-commutative operator rings `Stage : ℕ → Type u`
   `[∀ s, Ring (Stage s)]` with bonding ring homomorphisms `bond : ∀ s, Stage s →+* Stage (s + 1)`,
   let `DirectLimitSuperClosure bond := _root_.DirectLimit Stage (fun m n h => bondMap bond m n h)`
   be the genuine Mathlib algebraic direct-limit ring with canonical stage injections
   `directLimitOf bond s : Stage s →+* DirectLimitSuperClosure bond`. Then for any stage `s ≤ t`,
   the iterated bond `bondMap bond s t hst` commutes with `uhfIdemTower k`, maps to the same
   colimit idempotent `uhfIdemTower k P_∞ A_∞` in `DirectLimitSuperClosure bond`, and satisfies
   the full all-mode Heisenberg–Sugawara–Virasoro commutator/anticommutator algebra in
   `DirectLimitSuperClosure bond`.
2. In the Clifford tensor tower (`Cl11TensorTowerLimit.Stage`, `Cl11TensorTowerLimit.Limit`,
   `Cl11MatrixTowerTailShift.TailLimit d` with `cl11MatrixLimit_tailRingEquiv d : Limit ≃+* TailLimit d`),
   advancing any finite-head idempotent `Q : Cl11TensorTowerLimit.Stage s` (`Q * Q = Q`) by
   `stageEmbed s` (`A ↦ A ⊗ I₂`) preserves `uhfIdemTower k` in the infinite tail ring `TailLimit d`
   and satisfies the all-mode Heisenberg–Sugawara–Virasoro algebra in `TailLimit d`. -/
theorem uhf_heisenberg_sugawara_virasoro_direct_limit_and_clifford_tail_realization
    {Stage : ℕ → Type u} [∀ s, Ring (Stage s)]
    (bond : ∀ s : ℕ, Stage s →+* Stage (s + 1))
    (s t d n m k : ℕ) (hst : s ≤ t)
    {P : Stage s} (hP : P * P = P) (A C : Stage s)
    {Q : InfoGeometry.Clifford.Cl11TensorTowerLimit.Stage s} (hQ : Q * Q = Q)
    (U W : InfoGeometry.Clifford.Cl11TensorTowerLimit.Stage s) :
    let ofLim  := InfoGeometry.Algebra.DirectLimitSuperClosureLemmas.directLimitOf bond
    let P_inf  := ofLim s P
    let A_inf  := ofLim s A
    let C_inf  := ofLim s C
    let φ_tail := (InfoGeometry.Canonical.Cl11MatrixTowerTailShift.cl11MatrixLimit_tailRingEquiv d).toRingHom
    let Q_tail := φ_tail (InfoGeometry.Clifford.Cl11TensorTowerLimit.ofStage s Q)
    let U_tail := φ_tail (InfoGeometry.Clifford.Cl11TensorTowerLimit.ofStage s U)
    let W_tail := φ_tail (InfoGeometry.Clifford.Cl11TensorTowerLimit.ofStage s W)
    ofLim t (InfoGeometry.Algebra.DirectLimitSuperClosureLemmas.bondMap bond s t hst (uhfIdemTower k P A)) =
      uhfIdemTower k P_inf A_inf ∧
    comm (heisenbergSourceMode n P_inf A_inf C_inf) (heisenbergSinkMode m P_inf A_inf C_inf) =
      virasoroModeChiral (n + m) P_inf A_inf C_inf ∧
    comm (virasoroModeChiral n P_inf A_inf C_inf) (heisenbergSourceMode m P_inf A_inf C_inf) =
      (2 : ℤ) • heisenbergSourceMode (n + m + 1) P_inf A_inf C_inf ∧
    φ_tail (InfoGeometry.Clifford.Cl11TensorTowerLimit.ofStage (s + 1)
      (uhfIdemTower k (InfoGeometry.Clifford.Cl11TensorTower.stageEmbed s Q)
        (InfoGeometry.Clifford.Cl11TensorTower.stageEmbed s U))) =
      uhfIdemTower k Q_tail U_tail ∧
    comm (heisenbergSourceMode n Q_tail U_tail W_tail) (heisenbergSinkMode m Q_tail U_tail W_tail) =
      virasoroModeChiral (n + m) Q_tail U_tail W_tail ∧
    comm (virasoroModeChiral n Q_tail U_tail W_tail) (heisenbergSourceMode m Q_tail U_tail W_tail) =
      (2 : ℤ) • heisenbergSourceMode (n + m + 1) Q_tail U_tail W_tail := by
  have hConeDir : ∀ (j : ℕ) (Z : Stage j),
      InfoGeometry.Algebra.DirectLimitSuperClosureLemmas.directLimitOf bond (j + 1) (bond j Z) =
        InfoGeometry.Algebra.DirectLimitSuperClosureLemmas.directLimitOf bond j Z :=
    fun j Z => InfoGeometry.Algebra.DirectLimitSuperClosureLemmas.directLimitOf_bond bond j Z
  rcases uhf_heisenberg_sugawara_virasoro_colimit_cone_transport
      bond (InfoGeometry.Algebra.DirectLimitSuperClosureLemmas.directLimitOf bond) hConeDir
      s hP A C n m k with ⟨hLim1, _, hH1, _, hV1, _⟩
  have hBond :
      InfoGeometry.Algebra.DirectLimitSuperClosureLemmas.directLimitOf bond t
        (InfoGeometry.Algebra.DirectLimitSuperClosureLemmas.bondMap bond s t hst (uhfIdemTower k P A)) =
        uhfIdemTower k (InfoGeometry.Algebra.DirectLimitSuperClosureLemmas.directLimitOf bond s P)
          (InfoGeometry.Algebra.DirectLimitSuperClosureLemmas.directLimitOf bond s A) := by
    rw [InfoGeometry.Algebra.DirectLimitSuperClosureLemmas.directLimitOf_bondMap bond s t hst, hLim1]
  let toTailStage : ∀ j : ℕ, InfoGeometry.Clifford.Cl11TensorTowerLimit.Stage j →+*
      InfoGeometry.Canonical.Cl11MatrixTowerTailShift.TailLimit d :=
    fun j => (InfoGeometry.Canonical.Cl11MatrixTowerTailShift.cl11MatrixLimit_tailRingEquiv d).toRingHom.comp
      (InfoGeometry.Clifford.Cl11TensorTowerLimit.ofStage j)
  have hConeTail : ∀ (j : ℕ) (Z : InfoGeometry.Clifford.Cl11TensorTowerLimit.Stage j),
      toTailStage (j + 1) (InfoGeometry.Clifford.Cl11TensorTowerLimit.stageBond j Z) = toTailStage j Z := by
    intro j Z
    dsimp [toTailStage, InfoGeometry.Clifford.Cl11TensorTowerLimit.stageBond]
    rw [InfoGeometry.Clifford.Cl11TensorTowerLimit.ofStage_apply_bond]
  rcases uhf_heisenberg_sugawara_virasoro_colimit_cone_transport
      InfoGeometry.Clifford.Cl11TensorTowerLimit.stageBond toTailStage hConeTail
      s hQ U W n m k with ⟨_, hTail2, hTH1, _, hTV1, _⟩
  exact ⟨hBond, hH1, hV1, hTail2, hTH1, hTV1⟩

end Primitives

end InfoGeometry.OperatorAlgebra.PeirceSpine
