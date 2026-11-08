/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Tactic

/-!
# Audit of a proposed four-dimensional `Cl(3,3)` generator assignment

The native `Cl_split 3` owner uses an eight-dimensional real spinor carrier.
This file records a concrete obstruction to the six proposed `2 × 2` tensor
assignments: the proposed image of `e₁` commutes with the proposed image of
`f₃`, whereas orthogonal positive and negative Clifford generators must
anticommute. Thus those assignments do not define the claimed Clifford
representation. The actual bivector identities and their `8 × 8` spinor
readout are proved in `Cl33BivectorLoxodromicBridge`.
-/

noncomputable section

namespace InfoGeometry.Clifford.Cl33TwistorLoxodromic

abbrev M₂ := Matrix (Fin 2) (Fin 2) ℝ
abbrev M₄Tensor := Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ

def τ₁ : M₂ := !![0, 1; 1, 0]
def τ₂ : M₂ := !![0, -1; 1, 0]
def τ₃ : M₂ := !![1, 0; 0, -1]

/-- The proposed four-dimensional images of `e₁` and `f₃`. -/
def proposedE₁ : M₄Tensor := Matrix.kronecker τ₁ τ₁
def proposedF₃ : M₄Tensor := Matrix.kronecker τ₂ τ₃

theorem τ₁_mul_τ₂ : τ₁ * τ₂ = τ₃ := by
  ext i j
  all_goals fin_cases i
  all_goals fin_cases j
  all_goals norm_num [τ₁, τ₂, τ₃, Matrix.mul_apply, Fin.sum_univ_two]

theorem τ₂_mul_τ₁ : τ₂ * τ₁ = -τ₃ := by
  ext i j
  all_goals fin_cases i
  all_goals fin_cases j
  all_goals norm_num [τ₁, τ₂, τ₃, Matrix.mul_apply, Fin.sum_univ_two]

theorem τ₁_mul_τ₃ : τ₁ * τ₃ = τ₂ := by
  ext i j
  all_goals fin_cases i
  all_goals fin_cases j
  all_goals norm_num [τ₁, τ₂, τ₃, Matrix.mul_apply, Fin.sum_univ_two]

theorem τ₃_mul_τ₁ : τ₃ * τ₁ = -τ₂ := by
  ext i j
  all_goals fin_cases i
  all_goals fin_cases j
  all_goals norm_num [τ₁, τ₂, τ₃, Matrix.mul_apply, Fin.sum_univ_two]

/-- The ordered product of the two proposed images. -/
theorem proposedE₁_mul_proposedF₃ :
    proposedE₁ * proposedF₃ = Matrix.kronecker τ₃ τ₂ := by
  rw [proposedE₁, proposedF₃]
  calc
    Matrix.kronecker τ₁ τ₁ * Matrix.kronecker τ₂ τ₃ =
        Matrix.kronecker (τ₁ * τ₂) (τ₁ * τ₃) :=
          (Matrix.mul_kronecker_mul τ₁ τ₂ τ₁ τ₃).symm
    _ = Matrix.kronecker τ₃ τ₂ := by rw [τ₁_mul_τ₂, τ₁_mul_τ₃]

/-- The reverse ordered product agrees with the forward one. -/
theorem proposedF₃_mul_proposedE₁ :
    proposedF₃ * proposedE₁ = Matrix.kronecker τ₃ τ₂ := by
  rw [proposedF₃, proposedE₁]
  calc
    Matrix.kronecker τ₂ τ₃ * Matrix.kronecker τ₁ τ₁ =
        Matrix.kronecker (τ₂ * τ₁) (τ₃ * τ₁) :=
          (Matrix.mul_kronecker_mul τ₂ τ₁ τ₃ τ₁).symm
    _ = Matrix.kronecker τ₃ τ₂ := by
      rw [τ₂_mul_τ₁, τ₃_mul_τ₁]
      ext i j
      rcases i with ⟨i₁, i₂⟩
      rcases j with ⟨j₁, j₂⟩
      simp

/-- The proposed images commute, since both tensor factors anticommute. -/
theorem proposedE₁_proposedF₃_commute :
    proposedE₁ * proposedF₃ = proposedF₃ * proposedE₁ := by
  rw [proposedE₁_mul_proposedF₃, proposedF₃_mul_proposedE₁]

/-- Their anticommutator is nonzero, contradicting the required
`{e₁,f₃}=0` Clifford relation. -/
theorem proposedE₁_proposedF₃_anticommutator_ne_zero :
    proposedE₁ * proposedF₃ + proposedF₃ * proposedE₁ ≠ 0 := by
  intro hzero
  rw [proposedE₁_mul_proposedF₃, proposedF₃_mul_proposedE₁] at hzero
  have hentry := congrArg (fun A : M₄Tensor => A (0, 0) (0, 1)) hzero
  norm_num [Matrix.kronecker_apply, τ₃, τ₂] at hentry

/-- Therefore the displayed six tensor matrices in the raw proposal cannot
be the images of an orthogonal `Cl(3,3)` basis. -/
theorem proposed_assignment_fails_Clifford_orthogonality :
    ¬ (proposedE₁ * proposedF₃ + proposedF₃ * proposedE₁ = 0) :=
  proposedE₁_proposedF₃_anticommutator_ne_zero

end InfoGeometry.Clifford.Cl33TwistorLoxodromic

end
