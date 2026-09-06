import InfoGeometry.OperatorAlgebra.CantorBernoulliFiniteMatrixRepresentationBridge
import Mathlib.Data.Matrix.Basis

/-!
# Finite matrix-unit representation as a star-algebra homomorphism

The preceding owner gives a linear matrix-unit readout.  Here we package the
same finite-stage map as a `StarAlgHom`; this remains a finite-stage theorem
and makes no claim about an infinite C⋆ completion.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.CantorBernoulliFiniteMatrixStarRepresentationBridge

open InfoGeometry.OperatorAlgebra.CantorBernoulliFiniteMatrixRepresentationBridge
open InfoGeometry.OperatorAlgebra.CantorBernoulliFiniteMatrixUnitBridge
open InfoGeometry.OperatorAlgebra.CantorBernoulliCuntzCStarRealization
open InfoGeometry.Canonical.UHFInductiveColimitBoundary

def bitWordMatrixStarRepresentation (n : ℕ) :
    BitWordMatrixStage n →⋆ₐ[ℂ] BoundedL2Operator where
  toFun := bitWordMatrixLinearRepresentation n
  map_one' := by
    exact bitWordMatrixLinearRepresentation_diagonal_sum n
  map_mul' A B := by
    classical
    have hsingle (i j k l : BitWord n) (a b : ℂ) :
        bitWordMatrixLinearRepresentation n
            (Matrix.single i j a * Matrix.single k l b) =
          if j = k then (a * b) • bitWordUnit n i l else 0 := by
      by_cases h : j = k
      · subst k
        rw [Matrix.single_mul_single_same]
        rw [bitWordMatrixLinearRepresentation_single_smul]
        simp
      · rw [Matrix.single_mul_single_of_ne (c := a) i j k h b]
        simp [h]
    rw [Matrix.matrix_eq_sum_single A, Matrix.matrix_eq_sum_single B]
    simp only [map_sum, map_smul,
      bitWordMatrixLinearRepresentation_single_smul]
    simp_rw [Finset.sum_mul, Finset.mul_sum]
    simp only [map_sum, bitWordMatrixLinearRepresentation_single_smul]
    apply Finset.sum_congr rfl
    intro x hx
    apply Finset.sum_congr rfl
    intro x₁ hx₁
    apply Finset.sum_congr rfl
    intro x₂ hx₂
    apply Finset.sum_congr rfl
    intro x₃ hx₃
    rw [hsingle]
    by_cases h₃ : x₃ = x
    · subst x₃
      by_cases h₁₂ : x₁ = x₂
      · subst x₂
        simp only [if_true]
        have hunit : bitWordUnit n x x₁ * bitWordUnit n x₁ x =
            bitWordUnit n x x := by
          change (bitWordUnit n x x₁).comp (bitWordUnit n x₁ x) = _
          simpa using (bitWordUnit_mul n x x₁ x₁ x)
        simp [hunit, smul_mul_assoc, mul_smul_comm, smul_smul, mul_comm]
      · simp only [if_neg h₁₂]
        have hunit : bitWordUnit n x x₁ * bitWordUnit n x₂ x =
            0 := by
          change (bitWordUnit n x x₁).comp (bitWordUnit n x₂ x) = _
          simpa [h₁₂] using (bitWordUnit_mul n x x₁ x₂ x)
        simp [hunit, smul_mul_assoc, mul_smul_comm, smul_smul]
    · by_cases h₁₂ : x₁ = x₂
      · subst x₂
        simp only [if_true]
        have hunit : bitWordUnit n x x₁ * bitWordUnit n x₁ x₃ =
            bitWordUnit n x x₃ := by
          change (bitWordUnit n x x₁).comp (bitWordUnit n x₁ x₃) = _
          simpa using (bitWordUnit_mul n x x₁ x₁ x₃)
        simp [hunit, smul_mul_assoc, mul_smul_comm, smul_smul, mul_comm]
      · simp only [if_neg h₁₂]
        have hunit : bitWordUnit n x x₁ * bitWordUnit n x₂ x₃ =
            0 := by
          change (bitWordUnit n x x₁).comp (bitWordUnit n x₂ x₃) = _
          simpa [h₁₂] using (bitWordUnit_mul n x x₁ x₂ x₃)
        simp [hunit, smul_mul_assoc, mul_smul_comm, smul_smul]
  map_zero' := by
    exact (bitWordMatrixLinearRepresentation n).map_zero
  map_add' A B := by
    exact (bitWordMatrixLinearRepresentation n).map_add A B
  commutes' r := by
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one]
    rw [map_smul, bitWordMatrixLinearRepresentation_diagonal_sum]
    ext f
    simp
  map_star' A := by
    classical
    have hstar (u v : BitWord n) (c : ℂ) :
        bitWordMatrixLinearRepresentation n
            (star (Matrix.single u v c)) =
          star (bitWordMatrixLinearRepresentation n (Matrix.single u v c)) := by
      have hmat : star (Matrix.single u v c) =
          Matrix.single v u (starRingEnd ℂ c) := by
        ext i j
        by_cases hu : u = j <;> by_cases hv : v = i <;>
          simp [Matrix.single, hu, hv]
      rw [hmat, bitWordMatrixLinearRepresentation_single_smul]
      conv_rhs =>
        rw [bitWordMatrixLinearRepresentation_single_smul]
      rw [star_smul, bitWordUnit_star]
      rfl
    rw [Matrix.matrix_eq_sum_single A]
    simp only [map_sum, star_sum]
    apply Finset.sum_congr rfl
    intro u hu
    apply Finset.sum_congr rfl
    intro v hv
    exact hstar u v (A u v)

@[simp] theorem bitWordMatrixStarRepresentation_apply_single
    (n : ℕ) (u v : BitWord n) :
      bitWordMatrixStarRepresentation n (Matrix.single u v 1) =
      bitWordUnit n u v := by
  change bitWordMatrixLinearRepresentation n (Matrix.single u v 1) = _
  exact bitWordMatrixLinearRepresentation_single n u v

end InfoGeometry.OperatorAlgebra.CantorBernoulliFiniteMatrixStarRepresentationBridge
