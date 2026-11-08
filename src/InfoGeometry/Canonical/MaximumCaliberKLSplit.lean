import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Topology.ThermodynamicGauge

/-!
# Maximum Caliber and KL Split

Finite theorem surface for the MaxCal path-current layer and the
symmetric/antisymmetric split of a directed KL-like divergence.

#### BUCKET 1: CLOSED FINITE THEOREMS
The directed divergence split, swap parity, diagonal identities, two-channel
MaxCal log-ratio identities, and thermodynamic-gauge commutator rewrites are
kernel-checked.

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT PREMISES
MaxCal optimization, KMS stationarity, detailed balance, and de Rham comparison
enter only through named hypotheses.

#### BUCKET 3: OPEN CLOSURE DEBT
Analytic MaxCal existence, quantum Markov semigroup construction, and continuum
cohomology identification are not claimed here.
-/

namespace InfoGeometry.Canonical.MaximumCaliberKLSplit

open InfoGeometry.Topology.ThermodynamicGauge

universe u v

noncomputable def symmetricDivergence
    {State : Type u} (D : State → State → ℝ) (p q : State) : ℝ :=
  (D p q + D q p) / 2

noncomputable def antisymmetricDivergence
    {State : Type u} (D : State → State → ℝ) (p q : State) : ℝ :=
  (D p q - D q p) / 2

/-- Jeffreys divergence, normalized as the symmetric half-sum. -/
noncomputable def jeffreysDivergence
    {State : Type u} (D : State → State → ℝ) (p q : State) : ℝ :=
  symmetricDivergence D p q

theorem divergence_eq_symmetric_add_antisymmetric
    {State : Type u} (D : State → State → ℝ) (p q : State) :
    D p q = symmetricDivergence D p q + antisymmetricDivergence D p q := by
  unfold symmetricDivergence antisymmetricDivergence
  ring

theorem reverseDivergence_eq_symmetric_sub_antisymmetric
    {State : Type u} (D : State → State → ℝ) (p q : State) :
    D q p = symmetricDivergence D p q - antisymmetricDivergence D p q := by
  unfold symmetricDivergence antisymmetricDivergence
  ring

theorem jeffreysDivergence_eq_symmetricDivergence
    {State : Type u} (D : State → State → ℝ) (p q : State) :
    jeffreysDivergence D p q = symmetricDivergence D p q := by
  rfl

theorem jeffreysDivergence_eq_half_sum
    {State : Type u} (D : State → State → ℝ) (p q : State) :
    jeffreysDivergence D p q = (D p q + D q p) / 2 := by
  rfl

theorem symmetricDivergence_swap
    {State : Type u} (D : State → State → ℝ) (p q : State) :
    symmetricDivergence D q p = symmetricDivergence D p q := by
  unfold symmetricDivergence
  ring

theorem antisymmetricDivergence_swap
    {State : Type u} (D : State → State → ℝ) (p q : State) :
    antisymmetricDivergence D q p = - antisymmetricDivergence D p q := by
  unfold antisymmetricDivergence
  ring

theorem jeffreysDivergence_swap
    {State : Type u} (D : State → State → ℝ) (p q : State) :
    jeffreysDivergence D q p = jeffreysDivergence D p q := by
  unfold jeffreysDivergence
  exact symmetricDivergence_swap D p q

theorem antisymmetricDivergence_self
    {State : Type u} (D : State → State → ℝ) (p : State) :
    antisymmetricDivergence D p p = 0 := by
  unfold antisymmetricDivergence
  ring

theorem antisymmetricDivergence_eq_zero_of_balance
    {State : Type u} (D : State → State → ℝ) (p q : State)
    (hbalance : D p q = D q p) :
    antisymmetricDivergence D p q = 0 := by
  unfold antisymmetricDivergence
  rw [hbalance]
  ring

theorem antisymmetricDivergence_eq_zero_iff_balance
    {State : Type u} (D : State → State → ℝ) (p q : State) :
    antisymmetricDivergence D p q = 0 ↔ D p q = D q p := by
  unfold antisymmetricDivergence
  constructor
  · intro hzero
    nlinarith
  · intro hbalance
    rw [hbalance]
    ring

theorem antisymmetricDivergence_ne_zero_of_broken_balance
    {State : Type u} (D : State → State → ℝ) (p q : State)
    (hbroken : D p q ≠ D q p) :
    antisymmetricDivergence D p q ≠ 0 := by
  intro hzero
  exact hbroken ((antisymmetricDivergence_eq_zero_iff_balance D p q).mp hzero)

theorem symmetricDivergence_self_eq_zero
    {State : Type u} (D : State → State → ℝ) (p : State)
    (hself : D p p = 0) :
    symmetricDivergence D p p = 0 := by
  unfold symmetricDivergence
  rw [hself]
  ring

theorem symmetricDivergence_nonneg_of_nonneg
    {State : Type u} (D : State → State → ℝ) (p q : State)
    (hpq : 0 ≤ D p q) (hqp : 0 ≤ D q p) :
    0 ≤ symmetricDivergence D p q := by
  unfold symmetricDivergence
  nlinarith

theorem jeffreysDivergence_nonneg_of_nonneg
    {State : Type u} (D : State → State → ℝ) (p q : State)
    (hpq : 0 ≤ D p q) (hqp : 0 ≤ D q p) :
    0 ≤ jeffreysDivergence D p q := by
  unfold jeffreysDivergence
  exact symmetricDivergence_nonneg_of_nonneg D p q hpq hqp

/-- Log forward/backward ratio produced by a two-channel MaxCal constraint pair. -/
def maxCalLogRatio (lambda forwardConstraint backwardConstraint : ℝ) : ℝ :=
  -lambda * (forwardConstraint - backwardConstraint)

theorem maxCalLogRatio_eq_zero_of_equal_constraints
    (lambda c : ℝ) :
    maxCalLogRatio lambda c c = 0 := by
  unfold maxCalLogRatio
  ring

theorem maxCalLogRatio_swap
    (lambda cf cb : ℝ) :
    maxCalLogRatio lambda cb cf = - maxCalLogRatio lambda cf cb := by
  unfold maxCalLogRatio
  ring

theorem maxCalLogRatio_eq_two_antisymmetric_current
    (lambda cf cb : ℝ) :
    maxCalLogRatio lambda cf cb =
      2 * antisymmetricDivergence (fun x _ : ℝ => -lambda * x) cf cb := by
  unfold maxCalLogRatio antisymmetricDivergence
  ring

/-- A finite MaxCal path constraint matches the thermodynamic transition commutator. -/
def MaxCalConstraintMatchesFlow
    {Op : Type v} [Ring Op]
    (flow : CausalNonequilibriumFlow Op)
    (pathConstraint : Op) : Prop :=
  pathConstraint = flow.d_ln_Q ∧
    flow.P_forward * flow.P_backward - flow.P_backward * flow.P_forward = pathConstraint

theorem pathConstraint_dlnQ_readout
    {Op : Type v} [Ring Op]
    {flow : CausalNonequilibriumFlow Op}
    {pathConstraint : Op}
    (hmatch : MaxCalConstraintMatchesFlow flow pathConstraint) :
    pathConstraint = flow.d_ln_Q :=
  hmatch.1

theorem entropy_production_eq_pathConstraint
    {Op : Type v} [Ring Op]
    {flow : CausalNonequilibriumFlow Op}
    {pathConstraint : Op}
    (hmatch : MaxCalConstraintMatchesFlow flow pathConstraint) :
    entropy_production flow = pathConstraint := by
  rw [entropy_production_eq_commutator]
  exact hmatch.2

theorem entropy_production_eq_dlnQ
    {Op : Type v} [Ring Op]
    {flow : CausalNonequilibriumFlow Op}
    {pathConstraint : Op}
    (hmatch : MaxCalConstraintMatchesFlow flow pathConstraint) :
    entropy_production flow = flow.d_ln_Q := by
  exact de_rham_potential_equals_entropy_production_of_commutator flow
    (by rw [hmatch.2, hmatch.1])

theorem antisymmetric_current_eq_pathConstraint
    {State : Type u}
    (D : State → State → ℝ) (p q : State)
    {flow : CausalNonequilibriumFlow ℝ}
    {pathConstraint : ℝ}
    (hmatch : MaxCalConstraintMatchesFlow flow pathConstraint)
    (hcalibrated :
      antisymmetricDivergence D p q = pathConstraint) :
    antisymmetricDivergence D p q = entropy_production flow := by
  rw [hcalibrated, entropy_production_eq_pathConstraint hmatch]

theorem antisymmetric_current_eq_dlnQ
    {State : Type u}
    (D : State → State → ℝ) (p q : State)
    {flow : CausalNonequilibriumFlow ℝ}
    {pathConstraint : ℝ}
    (hmatch : MaxCalConstraintMatchesFlow flow pathConstraint)
    (hcalibrated :
      antisymmetricDivergence D p q = pathConstraint) :
    antisymmetricDivergence D p q = flow.d_ln_Q := by
  rw [hcalibrated, pathConstraint_dlnQ_readout hmatch]

theorem maxCal_state_stationary
    {State : Type u}
    (transition : State → State)
    (markovState kmsState : State)
    (hstationary : transition kmsState = kmsState)
    (hselect : markovState = kmsState) :
    transition markovState = markovState := by
  rw [hselect]
  exact hstationary

end InfoGeometry.Canonical.MaximumCaliberKLSplit
