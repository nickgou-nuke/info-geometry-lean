/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Clifford.Cl11GradedTensorMorita
import InfoGeometry.Clifford.GradedTensorCutRank
import Mathlib.RingTheory.MatrixAlgebra

/-!
# Cut rank of the actual graded Clifford head untwist

The existing native graded tensor equivalence and the ordinary tensor/matrix
equivalence give two real tensor coordinate systems for the same matrix.
Their difference is proved to be the controlled parity twist, with right
multiplication by the native Clifford volume on the left factor. The general
cut-rank inequalities therefore apply to the actual untwisting map over any
graded coefficient algebra, including infinite-dimensional noncommutative ones.

This is the one-head cut. It does not identify all cuts of an iterated train
or prove a tensor-train minimality theorem.
-/

noncomputable section

open scoped Matrix Matrix.Module TensorProduct

namespace InfoGeometry.Clifford.Cl11UntwistCutRank

open InfoGeometry.Clifford.Cl11Matrix
open InfoGeometry.Clifford.Cl11GradedMorita
open InfoGeometry.Clifford.Cl11GradedTensorMorita
open InfoGeometry.Clifford.GradedTensorCutRank

universe u
variable {A : Type u} [Ring A] [Algebra ℝ A]

/-- Ordinary tensor/matrix coordinates, built from native algebra equivalences. -/
def ordinaryMatrixEquiv : CliffordAlgebra q11 ⊗[ℝ] A ≃ₐ[ℝ] Matrix (Fin 2) (Fin 2) A :=
  (Algebra.TensorProduct.congr cl11StandardEquiv (AlgEquiv.refl : A ≃ₐ[ℝ] A)).trans
    ((Algebra.TensorProduct.comm ℝ Mat2 A).trans (matrixEquivTensor (Fin 2) ℝ A).symm)

/-- Only the real head coefficients move past the arbitrary operator coefficient. -/
theorem ordinaryMatrixEquiv_tmul_entry (x : CliffordAlgebra q11) (a : A) (i j : Fin 2) :
    ordinaryMatrixEquiv (x ⊗ₜ[ℝ] a) i j = cl11StandardEquiv x i j • a := by
  change a * algebraMap ℝ A (cl11StandardEquiv x i j) = _
  rw [Algebra.smul_def]
  exact (Algebra.commutes _ _).symm

/-- Ordinary tensor coordinates retain the full noncommuting matrix-unit pair. -/
theorem ordinary_tensor_noncommuting [Nontrivial A] :
    ∃ x y : CliffordAlgebra q11 ⊗[ℝ] A, ¬Commute x y := by
  refine ⟨ordinaryMatrixEquiv.symm (Matrix.single (0 : Fin 2) 1 (1 : A)),
    ordinaryMatrixEquiv.symm (Matrix.single (1 : Fin 2) 0 (1 : A)), ?_⟩
  intro h
  apply InfoGeometry.OperatorAlgebra.GradedMatrixMorita.matrix_units_noncomm (A := A)
  have hm := congrArg ordinaryMatrixEquiv h.eq
  simpa only [map_mul, AlgEquiv.apply_symm_apply,
    InfoGeometry.OperatorAlgebra.GradedMatrixMorita.upperMatrixUnit,
    InfoGeometry.OperatorAlgebra.GradedMatrixMorita.lowerMatrixUnit] using hm

/-- The Clifford volume supplies the actual left controlled involution. -/
theorem volumeRight_involutive :
    (LinearMap.mulRight ℝ J1_cl).comp (LinearMap.mulRight ℝ J1_cl) = LinearMap.id := by
  ext x
  change (x * J1_cl) * J1_cl = x
  rw [mul_assoc, J1_cl_sq, mul_one]

variable (𝒜 : ZMod 2 → Submodule ℝ A) [GradedAlgebra 𝒜]
variable (θ : A ≃ₐ[ℝ] A)
variable (hEven : ∀ {a : A}, a ∈ 𝒜 0 → θ a = a)
variable (hOdd : ∀ {a : A}, a ∈ 𝒜 1 → θ a = -a)

/-- The actual graded lift agrees with the constructed controlled twist on
every simple tensor, including inhomogeneous coefficient elements. -/
theorem ordinaryMatrixEquiv_parityTwist_tmul (x : CliffordAlgebra q11) (a : A) :
    ordinaryMatrixEquiv
        (parityTwist (LinearMap.mulRight ℝ J1_cl) θ.toLinearMap (x ⊗ₜ[ℝ] a)) =
      tensorToMatrix 𝒜 θ hEven hOdd (x ᵍ⊗ₜ a) := by
  rw [parityTwist_tmul, map_add, tensorToMatrix_tmul_matrix]
  ext i j
  simp only [Matrix.add_apply, ordinaryMatrixEquiv_tmul_entry,
    LinearMap.mulRight_apply, map_mul, cl11StandardEquiv_J1_cl,
    AlgEquiv.toLinearMap_apply]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Eplus] <;> module

/-- Exact coordinate identity on the entire genuine native graded tensor product. -/
theorem ordinaryMatrixEquiv_parityTwist
    (z : CliffordAlgebra.evenOdd q11 ᵍ⊗[ℝ] 𝒜) :
    ordinaryMatrixEquiv
        (parityTwist (LinearMap.mulRight ℝ J1_cl) θ.toLinearMap
          ((GradedTensorProduct.of ℝ (CliffordAlgebra.evenOdd q11) 𝒜).symm z)) =
      tensorMatrixEquiv 𝒜 θ hEven hOdd z := by
  obtain ⟨t, rfl⟩ :=
    (GradedTensorProduct.of ℝ (CliffordAlgebra.evenOdd q11) 𝒜).surjective z
  induction t with
  | tmul x a => exact ordinaryMatrixEquiv_parityTwist_tmul 𝒜 θ hEven hOdd x a
  | add s t hs ht => simpa only [map_add] using congrArg₂ (· + ·) hs ht

/-- The untwisted coordinates are derived from the two existing algebra
presentations, rather than defined to make a rank identity true. -/
theorem untwist_coordinates
    (z : CliffordAlgebra.evenOdd q11 ᵍ⊗[ℝ] 𝒜) :
    ordinaryMatrixEquiv.symm (tensorMatrixEquiv 𝒜 θ hEven hOdd z) =
      parityTwist (LinearMap.mulRight ℝ J1_cl) θ.toLinearMap
        ((GradedTensorProduct.of ℝ (CliffordAlgebra.evenOdd q11) 𝒜).symm z) := by
  apply ordinaryMatrixEquiv.injective
  rw [AlgEquiv.apply_symm_apply, ordinaryMatrixEquiv_parityTwist]

local instance : FiniteDimensional ℝ (CliffordAlgebra q11) :=
  LinearEquiv.finiteDimensional cl11StandardEquiv.symm.toLinearEquiv

/-- The factor-two estimate for the actual one-head graded untwisting map. -/
theorem untwist_cutRank_bounds
    (z : CliffordAlgebra.evenOdd q11 ᵍ⊗[ℝ] 𝒜) :
    cutRank (ordinaryMatrixEquiv.symm (tensorMatrixEquiv 𝒜 θ hEven hOdd z)) ≤
        2 * cutRank ((GradedTensorProduct.of ℝ (CliffordAlgebra.evenOdd q11) 𝒜).symm z) ∧
      cutRank ((GradedTensorProduct.of ℝ (CliffordAlgebra.evenOdd q11) 𝒜).symm z) ≤
        2 * cutRank (ordinaryMatrixEquiv.symm (tensorMatrixEquiv 𝒜 θ hEven hOdd z)) := by
  rw [untwist_coordinates]
  have hθ : θ.toLinearMap.comp θ.toLinearMap = LinearMap.id := by
    ext a
    exact coefficientParity_involutive 𝒜 θ hEven hOdd a
  exact cutRank_parityTwist_bounds _ _ volumeRight_involutive hθ _

/-- An arbitrary terminal coefficient algebra leaves the four-dimensional
head bound intact, without a finite-dimensional hypothesis on the tail. -/
theorem untwist_cutRank_le_four
    (z : CliffordAlgebra.evenOdd q11 ᵍ⊗[ℝ] 𝒜) :
    cutRank (ordinaryMatrixEquiv.symm (tensorMatrixEquiv 𝒜 θ hEven hOdd z)) ≤ 4 := by
  simpa only [finrank_cl11] using
    cutRank_le_left (ordinaryMatrixEquiv.symm (tensorMatrixEquiv 𝒜 θ hEven hOdd z))

end InfoGeometry.Clifford.Cl11UntwistCutRank
