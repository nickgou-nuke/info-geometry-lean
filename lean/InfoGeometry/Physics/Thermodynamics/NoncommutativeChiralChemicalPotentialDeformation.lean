import InfoGeometry.Physics.BdGChiralBlockMatrix
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NoncommRing

namespace InfoGeometry.Physics.Thermodynamics

open InfoGeometry.Physics
open Matrix

noncomputable section

/-!
# Noncommutative chemical-potential conjugation

The coefficient algebra `A` is only assumed to be a ring with an `ℝ`-algebra
structure.  Thus `A` may be noncommutative (for example, a matrix algebra).
The Gibbs factor uses the central image of real scalars through `algebraMap`.
No scalar commutativity of the observable coefficient is assumed.
-/

variable {A : Type*} [Ring A] [Algebra ℝ A]

/-- The central diagonal Gibbs factor on the two chiral sectors. -/
noncomputable def ncGibbsFactor (μ : ℝ) : BdGBlock A :=
  !![algebraMap ℝ A (Real.exp μ), 0;
     0, algebraMap ℝ A (Real.exp (-μ))]

@[simp] theorem ncGibbsFactor_zero :
    ncGibbsFactor (A := A) 0 = (1 : BdGBlock A) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ncGibbsFactor]

@[simp] theorem ncGibbsFactor_inv (μ : ℝ) :
    ncGibbsFactor μ * ncGibbsFactor (-μ) = (1 : BdGBlock A) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ncGibbsFactor, Matrix.mul_apply, Fin.sum_univ_two,
      ← map_mul, ← Real.exp_add]

@[simp] theorem ncGibbsFactor_add (μ ν : ℝ) :
    ncGibbsFactor (A := A) (μ + ν) =
      ncGibbsFactor (A := A) μ * ncGibbsFactor (A := A) ν := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ncGibbsFactor, Matrix.mul_apply, Fin.sum_univ_two,
      ← map_mul, Real.exp_add]
  · congr 1
    ring

@[simp] theorem ncGibbsFactor_commutes_with_chiralGrading (μ : ℝ) :
    ncGibbsFactor (A := A) μ * (chiralGrading : BdGBlock A) =
      (chiralGrading : BdGBlock A) * ncGibbsFactor (A := A) μ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ncGibbsFactor, chiralGrading, Matrix.mul_apply,
      Fin.sum_univ_two]

/-- Conjugation by the native noncommutative Gibbs factor. -/
noncomputable def ncChemicalPotentialFlow
    (μ : ℝ) (D : BdGBlock A) : BdGBlock A :=
  ncGibbsFactor (A := A) μ * D * ncGibbsFactor (A := A) (-μ)

theorem ncChemicalPotentialFlow_zero (D : BdGBlock A) :
    ncChemicalPotentialFlow 0 D = D := by
  simp [ncChemicalPotentialFlow]

theorem ncChemicalPotentialFlow_add (μ ν : ℝ) (D : BdGBlock A) :
    ncChemicalPotentialFlow (μ + ν) D =
      ncChemicalPotentialFlow μ (ncChemicalPotentialFlow ν D) := by
  unfold ncChemicalPotentialFlow
  rw [ncGibbsFactor_add μ ν]
  have hneg : -(μ + ν) = (-ν) + (-μ) := by ring
  rw [hneg, ncGibbsFactor_add (-ν) (-μ)]
  noncomm_ring

theorem ncChemicalPotentialFlow_inverse (μ : ℝ) (D : BdGBlock A) :
    ncChemicalPotentialFlow (-μ) (ncChemicalPotentialFlow μ D) = D := by
  unfold ncChemicalPotentialFlow
  simp only [neg_neg]
  have hinv :
      ncGibbsFactor (A := A) (-μ) * ncGibbsFactor (A := A) μ =
        (1 : BdGBlock A) := by
    simpa using (ncGibbsFactor_inv (A := A) (-μ))
  calc
    ncGibbsFactor (A := A) (-μ) *
          (ncGibbsFactor (A := A) μ * D *
            ncGibbsFactor (A := A) (-μ)) *
          ncGibbsFactor (A := A) μ =
        (ncGibbsFactor (A := A) (-μ) * ncGibbsFactor (A := A) μ) * D *
          (ncGibbsFactor (A := A) (-μ) * ncGibbsFactor (A := A) μ) := by
            noncomm_ring
    _ = D := by
      rw [hinv]
      simp

theorem ncChemicalPotentialFlow_preserves_oddness
    (μ : ℝ) (D : BdGBlock A)
    (hD : D * (chiralGrading : BdGBlock A) +
      (chiralGrading : BdGBlock A) * D = 0) :
    ncChemicalPotentialFlow μ D * (chiralGrading : BdGBlock A) +
        (chiralGrading : BdGBlock A) * ncChemicalPotentialFlow μ D = 0 := by
  unfold ncChemicalPotentialFlow
  have hG := ncGibbsFactor_commutes_with_chiralGrading (A := A) μ
  have hGinv := ncGibbsFactor_commutes_with_chiralGrading (A := A) (-μ)
  calc
    ncGibbsFactor (A := A) μ * D * ncGibbsFactor (A := A) (-μ) *
          chiralGrading + chiralGrading *
            (ncGibbsFactor (A := A) μ * D *
              ncGibbsFactor (A := A) (-μ)) =
            ncGibbsFactor (A := A) μ * D *
              (ncGibbsFactor (A := A) (-μ) * chiralGrading) +
            (chiralGrading * ncGibbsFactor (A := A) μ) * D *
              ncGibbsFactor (A := A) (-μ) := by
              noncomm_ring
    _ = ncGibbsFactor (A := A) μ * D *
          (chiralGrading * ncGibbsFactor (A := A) (-μ)) +
        (ncGibbsFactor (A := A) μ * chiralGrading) * D *
          ncGibbsFactor (A := A) (-μ) := by
            rw [hGinv, ← hG]
    _ = ncGibbsFactor (A := A) μ *
          (D * chiralGrading + chiralGrading * D) *
            ncGibbsFactor (A := A) (-μ) := by
              noncomm_ring
    _ = 0 := by rw [hD]; simp

theorem ncDiracFlow_preserves_chiral_oddness
    [StarRing A] (μ Δ : ℝ) :
    ncChemicalPotentialFlow μ (diracOperator (algebraMap ℝ A Δ)) *
          (chiralGrading : BdGBlock A) +
        (chiralGrading : BdGBlock A) *
          ncChemicalPotentialFlow μ (diracOperator (algebraMap ℝ A Δ)) = 0 := by
  apply ncChemicalPotentialFlow_preserves_oddness
  exact dirac_anticommutes_with_chirality _

/-! The square transport is stated before any special commutation claim. -/

theorem ncChemicalPotentialFlow_square (μ : ℝ) (D : BdGBlock A) :
    ncChemicalPotentialFlow μ D * ncChemicalPotentialFlow μ D =
      ncGibbsFactor (A := A) μ * (D * D) *
        ncGibbsFactor (A := A) (-μ) := by
  unfold ncChemicalPotentialFlow
  have hinv :
      ncGibbsFactor (A := A) (-μ) * ncGibbsFactor (A := A) μ =
        (1 : BdGBlock A) := by
    simpa using (ncGibbsFactor_inv (A := A) (-μ))
  calc
    ncGibbsFactor (A := A) μ * D * ncGibbsFactor (A := A) (-μ) *
          (ncGibbsFactor (A := A) μ * D *
            ncGibbsFactor (A := A) (-μ)) =
        ncGibbsFactor (A := A) μ * D *
          (ncGibbsFactor (A := A) (-μ) *
            ncGibbsFactor (A := A) μ) * D *
            ncGibbsFactor (A := A) (-μ) := by
            noncomm_ring
    _ = ncGibbsFactor (A := A) μ * (D * D) *
          ncGibbsFactor (A := A) (-μ) := by
      rw [hinv]
      noncomm_ring

theorem ncChemicalPotentialFlow_sq_of_commutes
    (μ : ℝ) (D : BdGBlock A)
    (hD : ncGibbsFactor (A := A) μ * (D * D) =
      (D * D) * ncGibbsFactor (A := A) μ) :
    ncChemicalPotentialFlow μ D * ncChemicalPotentialFlow μ D = D * D := by
  rw [ncChemicalPotentialFlow_square]
  calc
    ncGibbsFactor (A := A) μ * (D * D) *
          ncGibbsFactor (A := A) (-μ) =
        (D * D) * ncGibbsFactor (A := A) μ *
          ncGibbsFactor (A := A) (-μ) := by rw [hD]
    _ = (D * D) * (ncGibbsFactor (A := A) μ *
          ncGibbsFactor (A := A) (-μ)) := by noncomm_ring
    _ = D * D := by simp

end

end InfoGeometry.Physics.Thermodynamics
