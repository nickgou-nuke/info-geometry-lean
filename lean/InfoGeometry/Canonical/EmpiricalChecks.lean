import InfoGeometry.Canonical.ChiralAnomaly
import InfoGeometry.Canonical.GrandCanonicalExperts
import InfoGeometry.Canonical.Thermo

/-!
# InfoGeometry.Canonical.EmpiricalChecks

Concrete finite-instance extraction lemmas that connect canonical theorem
surfaces to directly checkable model configurations.
-/

namespace InfoGeometry.Canonical.EmpiricalChecks

open scoped BigOperators
open InfoGeometry.Canonical.ChiralAnomaly
open InfoGeometry.Canonical.MoE
open InfoGeometry.Thermo

section FiniteThermo

/-- Concrete two-state sample space used for finite Gibbs checks. -/
abbrev TwoState : Type := Fin 2

/-- A fixed nontrivial two-state energy profile. -/
def twoStateEnergy : TwoState → ℝ
  | ⟨0, _⟩ => 0
  | _ => 1

/-- Lemma `twoState_partition_pos`. -/
lemma twoState_partition_pos (ε : ℝ) :
    0 < Z twoStateEnergy ε :=
  Z_pos (E := twoStateEnergy) ε

/-- Lemma `twoState_gibbs_sum_one`. -/
lemma twoState_gibbs_sum_one (ε : ℝ) :
    ∑ ω : TwoState, gibbsProb twoStateEnergy ε ω = 1 :=
  gibbsProb_sum_one (E := twoStateEnergy) ε

/-- Lemma `twoState_freeEnergy_identity`. -/
lemma twoState_freeEnergy_identity (ε : ℝ) (hε : ε ≠ 0) :
    freeEnergy twoStateEnergy ε
      = internalEnergy twoStateEnergy ε - ε * shannonEntropy twoStateEnergy ε :=
  freeEnergy_eq_internal_sub_scale_entropy (E := twoStateEnergy) ε hε

/-- Lemma `twoState_freeEnergy_identity_unit`. -/
lemma twoState_freeEnergy_identity_unit :
    freeEnergy twoStateEnergy 1
      = internalEnergy twoStateEnergy 1 - shannonEntropy twoStateEnergy 1 := by
  simpa using twoState_freeEnergy_identity (ε := (1 : ℝ)) one_ne_zero

end FiniteThermo

section RoutingBounds

variable {V : Type*} [NormedAddCommGroup V]
variable (n : Nat) [Nonempty (Fin n)]

/-- Lemma `switch_selectedRoutingEpsilon_le_one`. -/
lemma switch_selectedRoutingEpsilon_le_one
    (β : ℝ) (x : Fin n → V) (hcol : IsBistochasticSwitch n β x)
    (label : PermMode n → CliffordLabel) :
    selectedRoutingEpsilon n (switchMatrix n β x)
      (switchMatrix_mem_doublyStochastic (n := n) β x hcol) label ≤ 1 := by
  exact selectedRoutingEpsilon_le_one (n := n) (M := switchMatrix n β x)
    (hM := switchMatrix_mem_doublyStochastic (n := n) β x hcol) label

end RoutingBounds

end InfoGeometry.Canonical.EmpiricalChecks

