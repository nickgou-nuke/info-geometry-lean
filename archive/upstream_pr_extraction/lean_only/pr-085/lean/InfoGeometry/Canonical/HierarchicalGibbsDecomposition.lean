import InfoGeometry.Canonical.HierarchicalGrandCanonical
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open scoped BigOperators

namespace InfoGeometry.Canonical

namespace HierarchicalGrandCanonical

variable {Sector : Type*} [Fintype Sector] [Nonempty Sector]
variable (State : Sector → Type*)
variable [∀ s, Fintype (State s)] [∀ s, Nonempty (State s)]

/-- Conditional canonical Gibbs weight inside one sector. -/
noncomputable def conditionalWeight
    (energy : ∀ s, State s → ℝ) (β : ℝ) (s : Sector) (x : State s) : ℝ :=
  canonicalWeight State energy β s x / canonicalPartition State energy β s

/-- Outer Gibbs weight assigned to a retained sector. -/
noncomputable def sectorWeight
    (energy : ∀ s, State s → ℝ) (particleNumber : Sector → ℝ)
    (β μ : ℝ) (s : Sector) : ℝ :=
  sectorNumerator State energy particleNumber β μ s /
    grandPartition State energy particleNumber β μ

/-- The conditional canonical weights normalize in each sector. -/
theorem sum_conditionalWeight_eq_one
    (energy : ∀ s, State s → ℝ) (β : ℝ) (s : Sector) :
    (∑ x, conditionalWeight State energy β s x) = 1 := by
  classical
  unfold conditionalWeight
  simp only [div_eq_mul_inv]
  rw [← Finset.sum_mul]
  exact mul_inv_cancel₀ (ne_of_gt (canonicalPartition_pos State energy β s))

/-- The outer sector weights normalize. -/
theorem sum_sectorWeight_eq_one
    (energy : ∀ s, State s → ℝ) (particleNumber : Sector → ℝ)
    (β μ : ℝ) :
    (∑ s, sectorWeight State energy particleNumber β μ s) = 1 := by
  classical
  unfold sectorWeight
  simp only [div_eq_mul_inv]
  rw [← Finset.sum_mul]
  exact mul_inv_cancel₀ (ne_of_gt (grandPartition_pos State energy particleNumber β μ))

/-- The joint hierarchical Gibbs weight factorizes into sector and conditional weights. -/
theorem jointWeight_eq_sectorWeight_mul_conditionalWeight
    (energy : ∀ s, State s → ℝ) (particleNumber : Sector → ℝ)
    (β μ : ℝ) (s : Sector) (x : State s) :
    jointWeight State energy particleNumber β μ s x =
      sectorWeight State energy particleNumber β μ s *
        conditionalWeight State energy β s x := by
  unfold jointWeight sectorWeight conditionalWeight jointNumerator sectorNumerator
  field_simp [ne_of_gt (canonicalPartition_pos State energy β s),
    ne_of_gt (grandPartition_pos State energy particleNumber β μ)]

/-- The joint surprisal is the energy plus the grand potential, in finite form. -/
noncomputable def jointSurprisal
    (energy : ∀ s, State s → ℝ) (particleNumber : Sector → ℝ)
    (β μ : ℝ) (s : Sector) (x : State s) : ℝ :=
  -Real.log (jointWeight State energy particleNumber β μ s x)

theorem jointSurprisal_eq_affineEnergy
    (energy : ∀ s, State s → ℝ) (particleNumber : Sector → ℝ)
    (β μ : ℝ) (s : Sector) (x : State s) :
    jointSurprisal State energy particleNumber β μ s x =
      β * energy s x - β * μ * particleNumber s +
        Real.log (grandPartition State energy particleNumber β μ) := by
  unfold jointSurprisal jointWeight jointNumerator canonicalWeight
  rw [Real.log_div]
  · rw [Real.log_mul]
    · rw [Real.log_exp, Real.log_exp]
      ring
    · exact ne_of_gt (Real.exp_pos _)
    · exact ne_of_gt (Real.exp_pos _)
  · exact ne_of_gt (mul_pos (Real.exp_pos _) (Real.exp_pos _))
  · exact ne_of_gt (grandPartition_pos State energy particleNumber β μ)

end HierarchicalGrandCanonical

end InfoGeometry.Canonical
