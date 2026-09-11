import InfoGeometry.Physics.Thermodynamics.ChiralChemicalPotentialDeformation
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases

namespace InfoGeometry.Physics.Thermodynamics

open InfoGeometry.Physics
open Matrix

noncomputable section

/-!
# Weighted/Krein adjointness for the chiral similarity deformation

The positive diagonal similarity factor does not preserve the ordinary
Euclidean adjoint.  The correct finite statement is pseudo-self-adjointness
with respect to the transported metric `ημ = Gμ⁻²`.
-/

/-- The transported diagonal metric operator `ημ = Gμ⁻²`. -/
noncomputable def chiralKreinMetric (μ : ℝ) : BdGBlock ℝ :=
  gibbsFactor (-2 * μ)

@[simp] theorem chiralKreinMetric_star (μ : ℝ) :
    star (chiralKreinMetric μ) = chiralKreinMetric μ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [chiralKreinMetric, gibbsFactor, Matrix.star_apply]

@[simp] theorem chiralKreinMetric_inverse (μ : ℝ) :
    chiralKreinMetric μ * gibbsFactor (2 * μ) = (1 : BdGBlock ℝ) := by
  unfold chiralKreinMetric
  have h : -2 * μ + 2 * μ = 0 := by ring
  rw [← gibbsFactor_add, h]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gibbsFactor]

/- The weighted metric is the pullback of the reference identity by the
   inverse positive chiral frame. -/
theorem chiralKreinMetric_eq_inverse_frame_pullback (μ : ℝ) :
    chiralKreinMetric μ =
      star (gibbsFactor (-μ)) * gibbsFactor (-μ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [chiralKreinMetric, gibbsFactor, Matrix.star_apply,
      Matrix.mul_apply, Fin.sum_univ_two]

/- The deformed Dirac block is self-adjoint for the weighted metric. -/
theorem chemicalPotentialDiracFlow_weighted_selfAdjoint
    (μ Δ : ℝ) :
    star (chemicalPotentialDiracFlow μ Δ) * chiralKreinMetric μ =
      chiralKreinMetric μ * chemicalPotentialDiracFlow μ Δ := by
  rw [chemicalPotentialDiracFlow_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [chiralKreinMetric, gibbsFactor, Matrix.star_apply,
      Matrix.mul_apply, Fin.sum_univ_two] <;>
    ring_nf

end

end InfoGeometry.Physics.Thermodynamics
