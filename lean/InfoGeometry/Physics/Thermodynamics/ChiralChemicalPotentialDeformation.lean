import InfoGeometry.Physics.BdGChiralBlockMatrix
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

namespace InfoGeometry.Physics.Thermodynamics

open InfoGeometry.Physics
open Matrix

noncomputable section

/-!
# Chiral similarity deformation on the native BdG block

This file records the finite matrix similarity deformation determined by the
diagonal weight `gibbsFactor μ = diag (exp μ, exp (-μ))`.

The core claims are finite and algebraic:

* the weight is invertible with inverse at `-μ`;
* conjugation by the weight rescales the off-diagonal Dirac legs;
* the deformed Dirac block anticommutes with the native chiral grading;
* the deformed square agrees with the undeformed square in this two-sector
  scalar-gap model.

This is a similarity deformation, not yet a KMS theorem or a detailed-balance
statement.
-/

/-- The diagonal exponential weight on the two BdG sectors. -/
noncomputable def gibbsFactor (mu : ℝ) : BdGBlock ℝ :=
  !![Real.exp mu, 0; 0, Real.exp (-mu)]

@[simp] theorem exp_mul_exp_neg (mu : ℝ) :
    Real.exp mu * Real.exp (-mu) = 1 := by
  rw [← Real.exp_add]
  simp

@[simp] theorem exp_neg_mul_exp (mu : ℝ) :
    Real.exp (-mu) * Real.exp mu = 1 := by
  simpa [mul_comm] using exp_mul_exp_neg mu

@[simp] theorem exp_mul_exp_self (mu : ℝ) :
    Real.exp mu * Real.exp mu = Real.exp (2 * mu) := by
  rw [← Real.exp_add]
  congr 1
  ring

@[simp] theorem exp_neg_mul_exp_neg (mu : ℝ) :
    Real.exp (-mu) * Real.exp (-mu) = Real.exp (-(2 * mu)) := by
  rw [← Real.exp_add]
  congr 1
  ring

@[simp] theorem gibbsFactor_add (mu nu : ℝ) :
    gibbsFactor (mu + nu) = gibbsFactor mu * gibbsFactor nu := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [gibbsFactor, Matrix.mul_apply, Fin.sum_univ_two, Real.exp_add, mul_comm] <;>
    ring

@[simp] theorem gibbsFactor_inv (mu : ℝ) :
    gibbsFactor mu * gibbsFactor (-mu) = (1 : BdGBlock ℝ) := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [gibbsFactor, Matrix.mul_apply, Fin.sum_univ_two]

@[simp] theorem gibbsFactor_neg_mul (mu : ℝ) :
    gibbsFactor (-mu) * gibbsFactor mu = (1 : BdGBlock ℝ) := by
  simpa using gibbsFactor_inv (-mu)

/-- Similarity deformation by the diagonal weight. -/
def chiralSimilarityFlow (mu : ℝ) (X : BdGBlock ℝ) : BdGBlock ℝ :=
  gibbsFactor mu * X * gibbsFactor (-mu)

@[simp] theorem gibbsFactor_zero : gibbsFactor 0 = (1 : BdGBlock ℝ) := by
  ext i j <;> fin_cases i <;> fin_cases j <;> simp [gibbsFactor]

/-- The explicit chemical-potential deformation of the native Dirac block. -/
def chemicalPotentialDiracFlow (mu Delta : ℝ) : BdGBlock ℝ :=
  chiralSimilarityFlow mu (diracOperator Delta)

@[simp] theorem chiralSimilarityFlow_zero (X : BdGBlock ℝ) :
    chiralSimilarityFlow 0 X = X := by
  simp [chiralSimilarityFlow, gibbsFactor_zero, mul_assoc]

theorem chiralSimilarityFlow_add (mu nu : ℝ) (X : BdGBlock ℝ) :
    chiralSimilarityFlow (mu + nu) X =
      chiralSimilarityFlow mu (chiralSimilarityFlow nu X) := by
  unfold chiralSimilarityFlow
  rw [gibbsFactor_add]
  have hneg : -(mu + nu) = (-nu) + (-mu) := by ring
  rw [hneg, gibbsFactor_add]
  simp [Matrix.mul_assoc]

@[simp] theorem chemicalPotentialDiracFlow_eq (mu Delta : ℝ) :
    chemicalPotentialDiracFlow mu Delta =
      !![0, Real.exp (2 * mu) * Delta;
         Real.exp (-(2 * mu)) * Delta, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [chemicalPotentialDiracFlow, chiralSimilarityFlow, gibbsFactor,
      diracOperator, Matrix.mul_apply, Fin.sum_univ_two, mul_comm, mul_left_comm,
      mul_assoc]

@[simp] theorem chiralSimilarityFlow_dirac (mu Delta : ℝ) :
    chiralSimilarityFlow mu (diracOperator Delta) =
      !![0, Real.exp (2 * mu) * Delta;
         Real.exp (-(2 * mu)) * Delta, 0] := by
  exact chemicalPotentialDiracFlow_eq mu Delta

@[simp] theorem gibbsFactor_commutes_with_chiralGrading (mu : ℝ) :
    gibbsFactor mu * chiralGrading =
      chiralGrading * gibbsFactor mu := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [gibbsFactor, chiralGrading, Matrix.mul_apply, Fin.sum_univ_two]

/-- The similarity-deformed Dirac block is still odd for the native grading. -/
theorem chiralSimilarityFlow_dirac_anticommutes (mu Delta : ℝ) :
    chiralSimilarityFlow mu (diracOperator Delta) * chiralGrading +
        chiralGrading * chiralSimilarityFlow mu (diracOperator Delta) = 0 := by
  rw [chiralSimilarityFlow_dirac]
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [chiralGrading, Matrix.mul_apply, Fin.sum_univ_two]

@[simp] theorem chemicalPotentialDiracFlow_anticommutes (mu Delta : ℝ) :
    chemicalPotentialDiracFlow mu Delta * chiralGrading +
        chiralGrading * chemicalPotentialDiracFlow mu Delta = 0 := by
  exact chiralSimilarityFlow_dirac_anticommutes mu Delta

/-- The native Dirac square. -/
@[simp] theorem diracOperator_sq (Delta : ℝ) :
    diracOperator Delta * diracOperator Delta =
      !![Delta * Delta, 0; 0, Delta * Delta] := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [diracOperator, Matrix.mul_apply, Fin.sum_univ_two]

/-- The square of the deformed Dirac is the same central square in this model. -/
theorem chiralSimilarityFlow_dirac_sq (mu Delta : ℝ) :
    chiralSimilarityFlow mu (diracOperator Delta) *
        chiralSimilarityFlow mu (diracOperator Delta) =
      diracOperator Delta * diracOperator Delta := by
  rw [chiralSimilarityFlow_dirac]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diracOperator, Matrix.mul_apply, Fin.sum_univ_two, mul_comm, mul_left_comm,
      mul_assoc]

@[simp] theorem chemicalPotentialDiracFlow_sq (mu Delta : ℝ) :
    chemicalPotentialDiracFlow mu Delta *
        chemicalPotentialDiracFlow mu Delta =
      diracOperator Delta * diracOperator Delta := by
  simpa using chiralSimilarityFlow_dirac_sq mu Delta

@[simp] theorem chemicalPotentialDiracFlow_sq_diagonal (mu Delta : ℝ) :
    chemicalPotentialDiracFlow mu Delta *
        chemicalPotentialDiracFlow mu Delta =
      !![Delta * Delta, 0; 0, Delta * Delta] := by
  rw [chemicalPotentialDiracFlow_sq, diracOperator_sq]

@[simp] theorem chemicalPotentialDiracFlow_sq_eq_diracSquare (mu Delta : ℝ) :
    chemicalPotentialDiracFlow mu Delta *
        chemicalPotentialDiracFlow mu Delta =
      diracSquare Delta := by
  rw [chemicalPotentialDiracFlow_sq, diracSquare]

end

end InfoGeometry.Physics.Thermodynamics
