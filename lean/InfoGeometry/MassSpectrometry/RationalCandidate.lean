/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.MassSpectrometry.VerifiedInferenceArchitecture

/-!
# Executable finite input validation

Proof-free rational data are checked before interpretation in the real-valued
owners. Condition indices refer to supplied observations; a selector in
`toModel` explicitly chooses how those kernels are used at other conditions.
-/

namespace InfoGeometry.MassSpectrometry

/-- Raw finite model input. No field presupposes correctness. -/
structure RationalCandidate (n k : ℕ) where
  peakMass : Fin n → ℚ
  intensity : Fin n → ℚ
  edge : Fin n → Fin n → Bool
  rank : Fin n → ℕ
  fragmentMass : Fin n → ℚ
  assignment : Matrix (Fin n) (Fin n) ℚ
  weight : Fin k → Matrix (Fin n) (Fin n) ℚ

namespace RationalCandidate
variable {n k : ℕ} (c : RationalCandidate n k)

/-- The exact finite conditions required by the existing model owners.
Empty spectra and empty condition tables are rejected explicitly. -/
def Valid : Prop :=
  0 < n ∧ 0 < k ∧
  (∀ i, 0 < c.peakMass i ∧ 0 ≤ c.intensity i ∧ 0 < c.fragmentMass i) ∧
  (∀ u v, c.edge u v = true →
    c.rank v < c.rank u ∧ c.fragmentMass v < c.fragmentMass u) ∧
  (∀ i j, (0 : ℚ) ≤ c.assignment i j) ∧
  (∀ i, ∑ j, c.assignment i j = 1) ∧
  (∀ j, ∑ i, c.assignment i j = 1) ∧
  (∀ e u v, (0 : ℚ) ≤ c.weight e u v) ∧
  (∀ e u v, c.weight e u v ≠ (0 : ℚ) → c.edge u v = true) ∧
  (∀ e u, ∑ v, c.weight e u v ≤ 1)

instance : Decidable c.Valid := by
  letI : ∀ i j, Decidable ((0 : ℚ) ≤ c.assignment i j) :=
    fun i j => Rat.instDecidableLe _ _
  letI : ∀ e u v, Decidable ((0 : ℚ) ≤ c.weight e u v) :=
    fun e u v => Rat.instDecidableLe _ _
  letI : ∀ e u v, Decidable (c.weight e u v = (0 : ℚ)) :=
    fun e u v => (inferInstance : DecidableEq ℚ) (c.weight e u v) 0
  unfold Valid
  infer_instance

/-- Computable acceptance, using exact rational comparisons and finite sums. -/
def check : Bool := decide c.Valid

@[simp] theorem check_eq_true_iff : c.check = true ↔ c.Valid := by
  simp [check]

/-- An executable proof-carrying result; rejected data produce `none`. -/
def validate : Option {x : RationalCandidate n k // x.Valid} :=
  if h : c.Valid then some ⟨c, h⟩ else none

theorem validate_eq_none_iff : c.validate = none ↔ ¬ c.Valid := by
  simp [validate]

theorem validate_preserves_input {x : {x : RationalCandidate n k // x.Valid}}
    (h : c.validate = some x) : x.val = c := by
  unfold validate at h
  split at h
  · cases Option.some.inj h
    rfl
  · contradiction

/-- Cast checked input to the existing positive real-valued peak carrier. -/
noncomputable def toSpectrum (h : c.Valid) : Spectrum n := fun i =>
  { mass := c.peakMass i
    intensity := c.intensity i
    mass_pos := by exact_mod_cast (h.2.2.1 i).1
    intensity_nonneg := by exact_mod_cast (h.2.2.1 i).2.1 }

/-- Boolean edges and checked ranks/masses construct the existing DAG owner. -/
noncomputable def toValuedDAG (h : c.Valid) : ValuedFragmentationDAG n where
  edge u v := c.edge u v = true
  rank := c.rank
  rank_decreases := fun huv => (h.2.2.2.1 _ _ huv).1
  massOf i := c.fragmentMass i
  mass_pos i := by exact_mod_cast (h.2.2.1 i).2.2
  mass_decreases := by
    intro u v huv
    exact_mod_cast (h.2.2.2.1 u v huv).2

/-- Rational assignment interpreted entrywise in the real owner. -/
noncomputable def realAssignment : AssignmentMatrix n :=
  fun i j => c.assignment i j

/-- Exact finite checks, not tolerance checks, discharge Birkhoff membership. -/
theorem realAssignment_soft (h : c.Valid) : IsSoftAssignment c.realAssignment := by
  apply mem_doublyStochastic_iff_sum.mpr
  refine ⟨?_, ?_, ?_⟩
  · intro i j
    change 0 ≤ (c.assignment i j : ℝ)
    exact_mod_cast h.2.2.2.2.1 i j
  · intro i
    change ∑ j, (c.assignment i j : ℝ) = 1
    exact_mod_cast h.2.2.2.2.2.1 i
  · intro j
    change ∑ i, (c.assignment i j : ℝ) = 1
    exact_mod_cast h.2.2.2.2.2.2.1 j

/-- Each supplied condition yields a checked substochastic grammar. -/
noncomputable def toGrammar (h : c.Valid) (e : Fin k) :
    StochasticGrammar (c.toValuedDAG h).toDAG where
  weight u v := c.weight e u v
  weight_nonneg u v := by exact_mod_cast h.2.2.2.2.2.2.2.1 e u v
  support := by
    intro u v huv
    apply h.2.2.2.2.2.2.2.2.1 e u v
    intro hz
    apply huv
    simp [hz]
  row_sum_le_one u := by
    exact_mod_cast h.2.2.2.2.2.2.2.2.2 e u

/-- Interpret accepted data using an explicit condition-to-table selection.
No interpolation or unobserved-condition accuracy is inferred. -/
noncomputable def toModel (h : c.Valid) (select : CollisionCondition → Fin k) :
    FiniteValuedFragmentationModel n where
  spectrum := c.toSpectrum h
  valuedDag := c.toValuedDAG h
  assignment := c.realAssignment
  assignment_soft := c.realAssignment_soft h
  grammar.kernel cond := c.toGrammar h (select cond)

/-- Acceptance constructs a model satisfying the existing admissibility API. -/
theorem check_sound (h : c.check = true) (select : CollisionCondition → Fin k) :
    IsStructurallyAdmissible (c.toModel (c.check_eq_true_iff.mp h) select) :=
  finiteValuedFragmentationModel_structurallyAdmissible
    (c.toModel (c.check_eq_true_iff.mp h) select)

/-- The model retains the checked transition table exactly under rational cast. -/
@[simp] theorem toModel_weight (h : c.Valid) (select : CollisionCondition → Fin k)
    (cond : CollisionCondition) (u v : Fin n) :
    ((c.toModel h select).grammarAt cond).weight u v = (c.weight (select cond) u v : ℝ) := rfl

end RationalCandidate
end InfoGeometry.MassSpectrometry
