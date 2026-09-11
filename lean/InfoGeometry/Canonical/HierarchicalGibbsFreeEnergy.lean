import InfoGeometry.Canonical.HierarchicalGibbsDecomposition
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open scoped BigOperators

namespace InfoGeometry.Canonical

namespace HierarchicalGrandCanonical

variable {Sector : Type*} [Fintype Sector] [Nonempty Sector]
variable (State : Sector → Type*)
variable [∀ s, Fintype (State s)] [∀ s, Nonempty (State s)]

/-- Canonical free energy of one finite sector. -/
noncomputable def canonicalFreeEnergy
    (energy : ∀ s, State s → ℝ) (β : ℝ) (s : Sector) : ℝ :=
  -(1 / β) * Real.log (canonicalPartition State energy β s)

/-- Effective grand-canonical potential of a sector. -/
noncomputable def effectiveSectorPotential
    (energy : ∀ s, State s → ℝ) (particleNumber : Sector → ℝ)
    (β μ : ℝ) (s : Sector) : ℝ :=
  canonicalFreeEnergy State energy β s - μ * particleNumber s

/-- Grand free energy of the full finite hierarchy. -/
noncomputable def grandFreeEnergy
    (energy : ∀ s, State s → ℝ) (particleNumber : Sector → ℝ)
    (β μ : ℝ) : ℝ :=
  -(1 / β) * Real.log (grandPartition State energy particleNumber β μ)

/-- Exponentiating minus β times a sector free energy recovers its partition. -/
theorem exp_neg_beta_mul_canonicalFreeEnergy_eq_canonicalPartition
    (energy : ∀ s, State s → ℝ) (β : ℝ) (s : Sector) (hβ : β ≠ 0) :
    Real.exp (-β * canonicalFreeEnergy State energy β s) =
      canonicalPartition State energy β s := by
  unfold canonicalFreeEnergy
  have hcancel :
      -β * (-(1 / β) * Real.log (canonicalPartition State energy β s)) =
        Real.log (canonicalPartition State energy β s) := by
    field_simp [hβ]
  rw [hcancel]
  exact Real.exp_log (canonicalPartition_pos State energy β s)

/-- Exponentiating minus β times the effective sector potential recovers its
    grand-canonical numerator. -/
theorem exp_neg_beta_mul_effectiveSectorPotential_eq_sectorNumerator
    (energy : ∀ s, State s → ℝ) (particleNumber : Sector → ℝ)
    (β μ : ℝ) (s : Sector) (hβ : β ≠ 0) :
    Real.exp (-β * effectiveSectorPotential State energy particleNumber β μ s) =
      sectorNumerator State energy particleNumber β μ s := by
  unfold effectiveSectorPotential
  have hcanonical :=
    exp_neg_beta_mul_canonicalFreeEnergy_eq_canonicalPartition
      State energy β s hβ
  unfold sectorNumerator
  rw [show -β * (canonicalFreeEnergy State energy β s - μ * particleNumber s) =
      -β * canonicalFreeEnergy State energy β s + β * μ * particleNumber s by ring]
  rw [Real.exp_add, hcanonical]
  ring

/-- The grand free energy exponentiates back to the total partition. -/
theorem exp_neg_beta_mul_grandFreeEnergy_eq_grandPartition
    (energy : ∀ s, State s → ℝ) (particleNumber : Sector → ℝ)
    (β μ : ℝ) (hβ : β ≠ 0) :
    Real.exp (-β * grandFreeEnergy State energy particleNumber β μ) =
      grandPartition State energy particleNumber β μ := by
  unfold grandFreeEnergy
  have hcancel :
      -β * (-(1 / β) * Real.log (grandPartition State energy particleNumber β μ)) =
        Real.log (grandPartition State energy particleNumber β μ) := by
    field_simp [hβ]
  rw [hcancel]
  exact Real.exp_log (grandPartition_pos State energy particleNumber β μ)

/-- The outer partition is the finite Gibbs partition of the effective sector
    potentials. -/
theorem grandPartition_eq_sum_exp_neg_beta_effectiveSectorPotential
    (energy : ∀ s, State s → ℝ) (particleNumber : Sector → ℝ)
    (β μ : ℝ) (hβ : β ≠ 0) :
    grandPartition State energy particleNumber β μ =
      ∑ s, Real.exp (-β * effectiveSectorPotential State energy particleNumber β μ s) := by
  classical
  unfold grandPartition
  apply Finset.sum_congr rfl
  intro s hs
  exact (exp_neg_beta_mul_effectiveSectorPotential_eq_sectorNumerator
    State energy particleNumber β μ s hβ).symm

end HierarchicalGrandCanonical

end InfoGeometry.Canonical
