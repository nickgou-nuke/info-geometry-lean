import Mathlib.Analysis.SpecialFunctions.Exp

open scoped BigOperators

namespace InfoGeometry.Canonical

/-!
# Finite hierarchical grand-canonical Gibbs ensembles

This module formalizes a two-level finite ensemble.  A sector is the retained
coarse state; conditional on a sector, microscopic states form a canonical
ensemble.  The sector partition functions are then mixed by an outer
grand-canonical weight.  No thermodynamic-limit statement is made here.
-/

namespace HierarchicalGrandCanonical

variable {Sector : Type*} [Fintype Sector] [Nonempty Sector]
variable (State : Sector → Type*)
variable [∀ s, Fintype (State s)] [∀ s, Nonempty (State s)]

/-- Microscopic Boltzmann weight inside a fixed sector. -/
noncomputable def canonicalWeight
    (energy : ∀ s, State s → ℝ) (β : ℝ) (s : Sector) (x : State s) : ℝ :=
  Real.exp (-β * energy s x)

/-- The canonical partition function of one sector. -/
noncomputable def canonicalPartition
    (energy : ∀ s, State s → ℝ) (β : ℝ) (s : Sector) : ℝ :=
  ∑ x, canonicalWeight State energy β s x

/-- The outer grand-canonical numerator for a sector. -/
noncomputable def sectorNumerator
    (energy : ∀ s, State s → ℝ) (particleNumber : Sector → ℝ)
    (β μ : ℝ) (s : Sector) : ℝ :=
  Real.exp (β * μ * particleNumber s) * canonicalPartition State energy β s

/-- The finite grand-canonical partition function obtained by coarse graining. -/
noncomputable def grandPartition
    (energy : ∀ s, State s → ℝ) (particleNumber : Sector → ℝ)
    (β μ : ℝ) : ℝ :=
  ∑ s, sectorNumerator State energy particleNumber β μ s

/-- Joint unnormalized weight of a sector and one of its microscopic states. -/
noncomputable def jointNumerator
    (energy : ∀ s, State s → ℝ) (particleNumber : Sector → ℝ)
    (β μ : ℝ) (s : Sector) (x : State s) : ℝ :=
  Real.exp (β * μ * particleNumber s) * canonicalWeight State energy β s x

/-- Normalized joint hierarchical Gibbs weight. -/
noncomputable def jointWeight
    (energy : ∀ s, State s → ℝ) (particleNumber : Sector → ℝ)
    (β μ : ℝ) (s : Sector) (x : State s) : ℝ :=
  jointNumerator State energy particleNumber β μ s x / grandPartition State energy particleNumber β μ

/-- Every canonical partition is strictly positive. -/
theorem canonicalPartition_pos
    (energy : ∀ s, State s → ℝ) (β : ℝ) (s : Sector) :
    0 < canonicalPartition State energy β s := by
  classical
  unfold canonicalPartition canonicalWeight
  exact Finset.sum_pos (fun x _ => Real.exp_pos _) Finset.univ_nonempty

/-- The nested grand partition is strictly positive. -/
theorem grandPartition_pos
    (energy : ∀ s, State s → ℝ) (particleNumber : Sector → ℝ)
    (β μ : ℝ) :
    0 < grandPartition State energy particleNumber β μ := by
  classical
  unfold grandPartition sectorNumerator
  apply Finset.sum_pos
  · intro s hs
    exact mul_pos (Real.exp_pos _) (canonicalPartition_pos State energy β s)
  · exact Finset.univ_nonempty

/-- Summing the joint numerator inside one sector gives its sector numerator. -/
theorem sum_jointNumerator_eq_sectorNumerator
    (energy : ∀ s, State s → ℝ) (particleNumber : Sector → ℝ)
    (β μ : ℝ) (s : Sector) :
    (∑ x, jointNumerator State energy particleNumber β μ s x) =
      sectorNumerator State energy particleNumber β μ s := by
  classical
  unfold jointNumerator sectorNumerator canonicalPartition canonicalWeight
  rw [Finset.mul_sum]

/-- The joint normalized mass of one sector is its outer Gibbs mass. -/
theorem sum_jointWeight_eq_sectorMass
    (energy : ∀ s, State s → ℝ) (particleNumber : Sector → ℝ)
    (β μ : ℝ) (s : Sector) :
    (∑ x, jointWeight State energy particleNumber β μ s x) =
      sectorNumerator State energy particleNumber β μ s /
        grandPartition State energy particleNumber β μ := by
  classical
  unfold jointWeight
  simp only [div_eq_mul_inv]
  rw [← Finset.sum_mul, sum_jointNumerator_eq_sectorNumerator]

/-- The nested partition equals the fully expanded two-level partition. -/
theorem grandPartition_eq_sum_jointNumerator
    (energy : ∀ s, State s → ℝ) (particleNumber : Sector → ℝ)
    (β μ : ℝ) :
    grandPartition State energy particleNumber β μ =
      ∑ s, ∑ x, jointNumerator State energy particleNumber β μ s x := by
  classical
  unfold grandPartition
  apply Finset.sum_congr rfl
  intro s hs
  exact (sum_jointNumerator_eq_sectorNumerator State energy particleNumber β μ s).symm

/-- The complete hierarchical Gibbs mass is normalized. -/
theorem sum_jointWeight_eq_one
    (energy : ∀ s, State s → ℝ) (particleNumber : Sector → ℝ)
    (β μ : ℝ) :
    (∑ s, ∑ x, jointWeight State energy particleNumber β μ s x) = 1 := by
  classical
  rw [show (∑ s, ∑ x, jointWeight State energy particleNumber β μ s x) =
      ∑ s, sectorNumerator State energy particleNumber β μ s /
        grandPartition State energy particleNumber β μ by
    apply Finset.sum_congr rfl
    intro s hs
    exact sum_jointWeight_eq_sectorMass State energy particleNumber β μ s]
  simp only [div_eq_mul_inv]
  rw [← Finset.sum_mul]
  rw [show (∑ s, sectorNumerator State energy particleNumber β μ s) =
      grandPartition State energy particleNumber β μ by rfl]
  exact mul_inv_cancel₀ (ne_of_gt (grandPartition_pos State energy particleNumber β μ))

end HierarchicalGrandCanonical

end InfoGeometry.Canonical
