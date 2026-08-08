import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
import Mathlib.LinearAlgebra.CliffordAlgebra.Grading
import Mathlib.LinearAlgebra.CliffordAlgebra.Conjugation
import InfoGeometry.Canonical.HestenesBivectorCarrier

namespace InfoGeometry.Canonical.HestenesBivectorCarrier

open CliffordAlgebra
open InfoGeometry.Canonical.CliffordParity
open HasVolumeElement
open HasSpacetimeBasis

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
variable (Q : QuadraticForm R M) [HasVolumeElement R M Q] [HasSpacetimeBasis Q]

theorem basisBivector_commutator_mem (i j : Fin 6) : basisBivector Q i * basisBivector Q j - basisBivector Q j * basisBivector Q i ∈ Bivector13 Q := by
  have h10 : ι Q (gamma Q 1) * ι Q (gamma Q 0) = - (ι Q (gamma Q 0) * ι Q (gamma Q 1)) := ι_mul_ι_swap_of_orthogonal Q (HasSpacetimeBasis.orthogonal (Q := Q) 0 1 (by decide))
  have h20 : ι Q (gamma Q 2) * ι Q (gamma Q 0) = - (ι Q (gamma Q 0) * ι Q (gamma Q 2)) := ι_mul_ι_swap_of_orthogonal Q (HasSpacetimeBasis.orthogonal (Q := Q) 0 2 (by decide))
  have h30 : ι Q (gamma Q 3) * ι Q (gamma Q 0) = - (ι Q (gamma Q 0) * ι Q (gamma Q 3)) := ι_mul_ι_swap_of_orthogonal Q (HasSpacetimeBasis.orthogonal (Q := Q) 0 3 (by decide))
  have h21 : ι Q (gamma Q 2) * ι Q (gamma Q 1) = - (ι Q (gamma Q 1) * ι Q (gamma Q 2)) := ι_mul_ι_swap_of_orthogonal Q (HasSpacetimeBasis.orthogonal (Q := Q) 1 2 (by decide))
  have h31 : ι Q (gamma Q 3) * ι Q (gamma Q 1) = - (ι Q (gamma Q 1) * ι Q (gamma Q 3)) := ι_mul_ι_swap_of_orthogonal Q (HasSpacetimeBasis.orthogonal (Q := Q) 1 3 (by decide))
  have h32 : ι Q (gamma Q 3) * ι Q (gamma Q 2) = - (ι Q (gamma Q 2) * ι Q (gamma Q 3)) := ι_mul_ι_swap_of_orthogonal Q (HasSpacetimeBasis.orthogonal (Q := Q) 2 3 (by decide))
  have h12 : ι Q (gamma Q 1) * ι Q (gamma Q 2) = - (ι Q (gamma Q 2) * ι Q (gamma Q 1)) := ι_mul_ι_swap_of_orthogonal Q (HasSpacetimeBasis.orthogonal (Q := Q) 2 1 (by decide))
  have h13 : ι Q (gamma Q 1) * ι Q (gamma Q 3) = - (ι Q (gamma Q 3) * ι Q (gamma Q 1)) := ι_mul_ι_swap_of_orthogonal Q (HasSpacetimeBasis.orthogonal (Q := Q) 3 1 (by decide))
  have sq0 := ι_sq_scalar Q (gamma Q 0)
  have sq1 := ι_sq_scalar Q (gamma Q 1)
  have sq2 := ι_sq_scalar Q (gamma Q 2)
  have sq3 := ι_sq_scalar Q (gamma Q 3)
  fin_cases i <;> fin_cases j
  · -- 0, 0
    dsimp [basisBivector]
    have H : ι Q (gamma Q 0) * ι Q (gamma Q 1) * (ι Q (gamma Q 0) * ι Q (gamma Q 1)) - ι Q (gamma Q 0) * ι Q (gamma Q 1) * (ι Q (gamma Q 0) * ι Q (gamma Q 1)) = 0 := by rw [sub_self]
    rw [H]; exact Submodule.zero_mem _
  · -- 0, 1
    dsimp [basisBivector]
    have H : (ι Q (gamma Q 0) * ι Q (gamma Q 1)) * (ι Q (gamma Q 0) * ι Q (gamma Q 2)) - (ι Q (gamma Q 0) * ι Q (gamma Q 2)) * (ι Q (gamma Q 0) * ι Q (gamma Q 1)) = (- 2 : R) • (algebraMap R _ (Q (gamma Q 0)) * (ι Q (gamma Q 1) * ι Q (gamma Q 2))) := by
      calc (ι Q (gamma Q 0) * ι Q (gamma Q 1)) * (ι Q (gamma Q 0) * ι Q (gamma Q 2)) - (ι Q (gamma Q 0) * ι Q (gamma Q 2)) * (ι Q (gamma Q 0) * ι Q (gamma Q 1))
        _ = ι Q (gamma Q 0) * (ι Q (gamma Q 1) * ι Q (gamma Q 0)) * ι Q (gamma Q 2) - ι Q (gamma Q 0) * (ι Q (gamma Q 2) * ι Q (gamma Q 0)) * ι Q (gamma Q 1) := by simp only [mul_assoc, ←mul_assoc]
        _ = ι Q (gamma Q 0) * - (ι Q (gamma Q 0) * ι Q (gamma Q 1)) * ι Q (gamma Q 2) - ι Q (gamma Q 0) * - (ι Q (gamma Q 0) * ι Q (gamma Q 2)) * ι Q (gamma Q 1) := by rw [h10, h20]
        _ = - ((ι Q (gamma Q 0) * ι Q (gamma Q 0)) * (ι Q (gamma Q 1) * ι Q (gamma Q 2))) + (ι Q (gamma Q 0) * ι Q (gamma Q 0)) * (ι Q (gamma Q 2) * ι Q (gamma Q 1)) := by simp only [mul_neg, neg_mul, sub_neg_eq_add, ←mul_assoc, mul_assoc]
        _ = - (algebraMap R _ (Q (gamma Q 0)) * (ι Q (gamma Q 1) * ι Q (gamma Q 2))) + algebraMap R _ (Q (gamma Q 0)) * (ι Q (gamma Q 2) * ι Q (gamma Q 1)) := by rw [sq0]
        _ = - (algebraMap R _ (Q (gamma Q 0)) * (ι Q (gamma Q 1) * ι Q (gamma Q 2))) + algebraMap R _ (Q (gamma Q 0)) * - (ι Q (gamma Q 1) * ι Q (gamma Q 2)) := by rw [h21]
        _ = - (algebraMap R _ (Q (gamma Q 0)) * (ι Q (gamma Q 1) * ι Q (gamma Q 2))) - algebraMap R _ (Q (gamma Q 0)) * (ι Q (gamma Q 1) * ι Q (gamma Q 2)) := by simp only [mul_neg, neg_mul, sub_eq_add_neg, ←mul_assoc, mul_assoc]
        _ = (- 2 : R) • (algebraMap R _ (Q (gamma Q 0)) * (ι Q (gamma Q 1) * ι Q (gamma Q 2))) := by simp only [neg_sub_neg, smul_eq_mul, neg_smul]; ring
    have H2 : ι Q (gamma Q 1) * ι Q (gamma Q 2) = basisBivector Q 5 := rfl
    rw [H, H2]; exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨5, rfl⟩))
  · -- 0, 2
    dsimp [basisBivector]
    have H : (ι Q (gamma Q 0) * ι Q (gamma Q 1)) * (ι Q (gamma Q 0) * ι Q (gamma Q 3)) - (ι Q (gamma Q 0) * ι Q (gamma Q 3)) * (ι Q (gamma Q 0) * ι Q (gamma Q 1)) = (- 2 : R) • (algebraMap R _ (Q (gamma Q 0)) * (ι Q (gamma Q 1) * ι Q (gamma Q 3))) := by
      calc (ι Q (gamma Q 0) * ι Q (gamma Q 1)) * (ι Q (gamma Q 0) * ι Q (gamma Q 3)) - (ι Q (gamma Q 0) * ι Q (gamma Q 3)) * (ι Q (gamma Q 0) * ι Q (gamma Q 1))
        _ = ι Q (gamma Q 0) * (ι Q (gamma Q 1) * ι Q (gamma Q 0)) * ι Q (gamma Q 3) - ι Q (gamma Q 0) * (ι Q (gamma Q 3) * ι Q (gamma Q 0)) * ι Q (gamma Q 1) := by simp only [mul_assoc, ←mul_assoc]
        _ = ι Q (gamma Q 0) * - (ι Q (gamma Q 0) * ι Q (gamma Q 1)) * ι Q (gamma Q 3) - ι Q (gamma Q 0) * - (ι Q (gamma Q 0) * ι Q (gamma Q 3)) * ι Q (gamma Q 1) := by rw [h10, h30]
        _ = - ((ι Q (gamma Q 0) * ι Q (gamma Q 0)) * (ι Q (gamma Q 1) * ι Q (gamma Q 3))) + (ι Q (gamma Q 0) * ι Q (gamma Q 0)) * (ι Q (gamma Q 3) * ι Q (gamma Q 1)) := by simp only [mul_neg, neg_mul, sub_neg_eq_add, ←mul_assoc, mul_assoc]
        _ = - (algebraMap R _ (Q (gamma Q 0)) * (ι Q (gamma Q 1) * ι Q (gamma Q 3))) + algebraMap R _ (Q (gamma Q 0)) * (ι Q (gamma Q 3) * ι Q (gamma Q 1)) := by rw [sq0]
        _ = - (algebraMap R _ (Q (gamma Q 0)) * (ι Q (gamma Q 1) * ι Q (gamma Q 3))) + algebraMap R _ (Q (gamma Q 0)) * - (ι Q (gamma Q 1) * ι Q (gamma Q 3)) := by rw [h31]
        _ = - (algebraMap R _ (Q (gamma Q 0)) * (ι Q (gamma Q 1) * ι Q (gamma Q 3))) - algebraMap R _ (Q (gamma Q 0)) * (ι Q (gamma Q 1) * ι Q (gamma Q 3)) := by simp only [mul_neg, neg_mul, sub_eq_add_neg, ←mul_assoc, mul_assoc]
        _ = (- 2 : R) • (algebraMap R _ (Q (gamma Q 0)) * (ι Q (gamma Q 1) * ι Q (gamma Q 3))) := by simp only [neg_sub_neg, smul_eq_mul, neg_smul]; ring
    have H2 : ι Q (gamma Q 1) * ι Q (gamma Q 3) = - basisBivector Q 4 := by rw [←h31]; rfl
    rw [H, H2]; simp only [mul_neg]; exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨4, rfl⟩))
  · -- 0, 3
    dsimp [basisBivector]
    have H : (ι Q (gamma Q 0) * ι Q (gamma Q 1)) * (ι Q (gamma Q 2) * ι Q (gamma Q 3)) - (ι Q (gamma Q 2) * ι Q (gamma Q 3)) * (ι Q (gamma Q 0) * ι Q (gamma Q 1)) = 0 := by
      calc (ι Q (gamma Q 0) * ι Q (gamma Q 1)) * (ι Q (gamma Q 2) * ι Q (gamma Q 3)) - (ι Q (gamma Q 2) * ι Q (gamma Q 3)) * (ι Q (gamma Q 0) * ι Q (gamma Q 1))
        _ = ι Q (gamma Q 0) * ι Q (gamma Q 1) * ι Q (gamma Q 2) * ι Q (gamma Q 3) - ι Q (gamma Q 2) * ι Q (gamma Q 3) * ι Q (gamma Q 0) * ι Q (gamma Q 1) := by simp only [mul_assoc]
        _ = ι Q (gamma Q 0) * ι Q (gamma Q 1) * ι Q (gamma Q 2) * ι Q (gamma Q 3) - ι Q (gamma Q 2) * (ι Q (gamma Q 3) * ι Q (gamma Q 0)) * ι Q (gamma Q 1) := by simp only [←mul_assoc, mul_assoc]
        _ = ι Q (gamma Q 0) * ι Q (gamma Q 1) * ι Q (gamma Q 2) * ι Q (gamma Q 3) - ι Q (gamma Q 2) * - (ι Q (gamma Q 0) * ι Q (gamma Q 3)) * ι Q (gamma Q 1) := by rw [h30]
        _ = ι Q (gamma Q 0) * ι Q (gamma Q 1) * ι Q (gamma Q 2) * ι Q (gamma Q 3) + (ι Q (gamma Q 2) * ι Q (gamma Q 0)) * ι Q (gamma Q 3) * ι Q (gamma Q 1) := by simp only [mul_neg, neg_mul, sub_neg_eq_add, ←mul_assoc, mul_assoc]
        _ = ι Q (gamma Q 0) * ι Q (gamma Q 1) * ι Q (gamma Q 2) * ι Q (gamma Q 3) + - (ι Q (gamma Q 0) * ι Q (gamma Q 2)) * ι Q (gamma Q 3) * ι Q (gamma Q 1) := by rw [h20]
        _ = ι Q (gamma Q 0) * ι Q (gamma Q 1) * ι Q (gamma Q 2) * ι Q (gamma Q 3) - ι Q (gamma Q 0) * ι Q (gamma Q 2) * (ι Q (gamma Q 3) * ι Q (gamma Q 1)) := by simp only [neg_mul, mul_neg, ←mul_assoc, mul_assoc, sub_eq_add_neg, neg_neg]
        _ = ι Q (gamma Q 0) * ι Q (gamma Q 1) * ι Q (gamma Q 2) * ι Q (gamma Q 3) - ι Q (gamma Q 0) * ι Q (gamma Q 2) * - (ι Q (gamma Q 1) * ι Q (gamma Q 3)) := by rw [h31]
        _ = ι Q (gamma Q 0) * ι Q (gamma Q 1) * ι Q (gamma Q 2) * ι Q (gamma Q 3) + ι Q (gamma Q 0) * (ι Q (gamma Q 2) * ι Q (gamma Q 1)) * ι Q (gamma Q 3) := by simp only [mul_neg, neg_mul, sub_neg_eq_add, ←mul_assoc, mul_assoc]
        _ = ι Q (gamma Q 0) * ι Q (gamma Q 1) * ι Q (gamma Q 2) * ι Q (gamma Q 3) + ι Q (gamma Q 0) * - (ι Q (gamma Q 1) * ι Q (gamma Q 2)) * ι Q (gamma Q 3) := by rw [h21]
        _ = ι Q (gamma Q 0) * ι Q (gamma Q 1) * ι Q (gamma Q 2) * ι Q (gamma Q 3) - ι Q (gamma Q 0) * ι Q (gamma Q 1) * ι Q (gamma Q 2) * ι Q (gamma Q 3) := by simp only [mul_neg, neg_mul, sub_eq_add_neg, ←mul_assoc, mul_assoc]
        _ = 0 := by rw [sub_self]
    rw [H]; exact Submodule.zero_mem _
  · -- 0, 4
    dsimp [basisBivector]
    have H : (ι Q (gamma Q 0) * ι Q (gamma Q 1)) * (ι Q (gamma Q 3) * ι Q (gamma Q 1)) - (ι Q (gamma Q 3) * ι Q (gamma Q 1)) * (ι Q (gamma Q 0) * ι Q (gamma Q 1)) = (- 2 : R) • (algebraMap R _ (Q (gamma Q 1)) * (ι Q (gamma Q 0) * ι Q (gamma Q 3))) := by
      calc (ι Q (gamma Q 0) * ι Q (gamma Q 1)) * (ι Q (gamma Q 3) * ι Q (gamma Q 1)) - (ι Q (gamma Q 3) * ι Q (gamma Q 1)) * (ι Q (gamma Q 0) * ι Q (gamma Q 1))
        _ = ι Q (gamma Q 0) * (ι Q (gamma Q 1) * ι Q (gamma Q 3)) * ι Q (gamma Q 1) - ι Q (gamma Q 3) * (ι Q (gamma Q 1) * ι Q (gamma Q 0)) * ι Q (gamma Q 1) := by simp only [mul_assoc, ←mul_assoc]
        _ = ι Q (gamma Q 0) * - (ι Q (gamma Q 3) * ι Q (gamma Q 1)) * ι Q (gamma Q 1) - ι Q (gamma Q 3) * - (ι Q (gamma Q 0) * ι Q (gamma Q 1)) * ι Q (gamma Q 1) := by rw [h31, h10]
        _ = - (ι Q (gamma Q 0) * ι Q (gamma Q 3) * (ι Q (gamma Q 1) * ι Q (gamma Q 1))) + ι Q (gamma Q 3) * ι Q (gamma Q 0) * (ι Q (gamma Q 1) * ι Q (gamma Q 1)) := by simp only [mul_neg, neg_mul, sub_neg_eq_add, ←mul_assoc, mul_assoc]
        _ = - (ι Q (gamma Q 0) * ι Q (gamma Q 3) * algebraMap R _ (Q (gamma Q 1))) + (ι Q (gamma Q 3) * ι Q (gamma Q 0)) * algebraMap R _ (Q (gamma Q 1)) := by rw [sq1]
        _ = - (algebraMap R _ (Q (gamma Q 1)) * (ι Q (gamma Q 0) * ι Q (gamma Q 3))) + algebraMap R _ (Q (gamma Q 1)) * (ι Q (gamma Q 3) * ι Q (gamma Q 0)) := by rw [Algebra.commutes, Algebra.commutes (Q (gamma Q 1))]
        _ = - (algebraMap R _ (Q (gamma Q 1)) * (ι Q (gamma Q 0) * ι Q (gamma Q 3))) + algebraMap R _ (Q (gamma Q 1)) * - (ι Q (gamma Q 0) * ι Q (gamma Q 3)) := by rw [h30]
        _ = - (algebraMap R _ (Q (gamma Q 1)) * (ι Q (gamma Q 0) * ι Q (gamma Q 3))) - algebraMap R _ (Q (gamma Q 1)) * (ι Q (gamma Q 0) * ι Q (gamma Q 3)) := by simp only [mul_neg, neg_mul, sub_eq_add_neg, ←mul_assoc, mul_assoc]
        _ = (- 2 : R) • (algebraMap R _ (Q (gamma Q 1)) * (ι Q (gamma Q 0) * ι Q (gamma Q 3))) := by simp only [neg_sub_neg, smul_eq_mul, neg_smul]; ring
    have H2 : ι Q (gamma Q 0) * ι Q (gamma Q 3) = basisBivector Q 2 := rfl
    rw [H, H2]; exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨2, rfl⟩))
  · -- 0, 5
    dsimp [basisBivector]
    have H : (ι Q (gamma Q 0) * ι Q (gamma Q 1)) * (ι Q (gamma Q 1) * ι Q (gamma Q 2)) - (ι Q (gamma Q 1) * ι Q (gamma Q 2)) * (ι Q (gamma Q 0) * ι Q (gamma Q 1)) = (2 : R) • (algebraMap R _ (Q (gamma Q 1)) * (ι Q (gamma Q 0) * ι Q (gamma Q 2))) := by
      calc (ι Q (gamma Q 0) * ι Q (gamma Q 1)) * (ι Q (gamma Q 1) * ι Q (gamma Q 2)) - (ι Q (gamma Q 1) * ι Q (gamma Q 2)) * (ι Q (gamma Q 0) * ι Q (gamma Q 1))
        _ = ι Q (gamma Q 0) * (ι Q (gamma Q 1) * ι Q (gamma Q 1)) * ι Q (gamma Q 2) - ι Q (gamma Q 1) * (ι Q (gamma Q 2) * ι Q (gamma Q 0)) * ι Q (gamma Q 1) := by simp only [mul_assoc, ←mul_assoc]
        _ = ι Q (gamma Q 0) * algebraMap R _ (Q (gamma Q 1)) * ι Q (gamma Q 2) - ι Q (gamma Q 1) * (ι Q (gamma Q 2) * ι Q (gamma Q 0)) * ι Q (gamma Q 1) := by rw [sq1]
        _ = algebraMap R _ (Q (gamma Q 1)) * (ι Q (gamma Q 0) * ι Q (gamma Q 2)) - ι Q (gamma Q 1) * - (ι Q (gamma Q 0) * ι Q (gamma Q 2)) * ι Q (gamma Q 1) := by rw [h20, Algebra.commutes]
        _ = algebraMap R _ (Q (gamma Q 1)) * (ι Q (gamma Q 0) * ι Q (gamma Q 2)) + (ι Q (gamma Q 1) * ι Q (gamma Q 0)) * ι Q (gamma Q 2) * ι Q (gamma Q 1) := by simp only [mul_neg, neg_mul, sub_neg_eq_add, ←mul_assoc, mul_assoc]
        _ = algebraMap R _ (Q (gamma Q 1)) * (ι Q (gamma Q 0) * ι Q (gamma Q 2)) + - (ι Q (gamma Q 0) * ι Q (gamma Q 1)) * ι Q (gamma Q 2) * ι Q (gamma Q 1) := by rw [h10]
        _ = algebraMap R _ (Q (gamma Q 1)) * (ι Q (gamma Q 0) * ι Q (gamma Q 2)) - ι Q (gamma Q 0) * (ι Q (gamma Q 1) * ι Q (gamma Q 2)) * ι Q (gamma Q 1) := by simp only [mul_neg, neg_mul, ←mul_assoc, mul_assoc, sub_eq_add_neg, neg_neg]
        _ = algebraMap R _ (Q (gamma Q 1)) * (ι Q (gamma Q 0) * ι Q (gamma Q 2)) - ι Q (gamma Q 0) * - (ι Q (gamma Q 2) * ι Q (gamma Q 1)) * ι Q (gamma Q 1) := by rw [h21]
        _ = algebraMap R _ (Q (gamma Q 1)) * (ι Q (gamma Q 0) * ι Q (gamma Q 2)) + ι Q (gamma Q 0) * ι Q (gamma Q 2) * (ι Q (gamma Q 1) * ι Q (gamma Q 1)) := by simp only [mul_neg, neg_mul, sub_neg_eq_add, ←mul_assoc, mul_assoc]
        _ = algebraMap R _ (Q (gamma Q 1)) * (ι Q (gamma Q 0) * ι Q (gamma Q 2)) + ι Q (gamma Q 0) * ι Q (gamma Q 2) * algebraMap R _ (Q (gamma Q 1)) := by rw [sq1]
        _ = algebraMap R _ (Q (gamma Q 1)) * (ι Q (gamma Q 0) * ι Q (gamma Q 2)) + algebraMap R _ (Q (gamma Q 1)) * (ι Q (gamma Q 0) * ι Q (gamma Q 2)) := by rw [Algebra.commutes (Q (gamma Q 1))]
        _ = (2 : R) • (algebraMap R _ (Q (gamma Q 1)) * (ι Q (gamma Q 0) * ι Q (gamma Q 2))) := by simp only [smul_eq_mul]; ring
    have H2 : ι Q (gamma Q 0) * ι Q (gamma Q 2) = basisBivector Q 1 := rfl
    rw [H, H2]; exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, rfl⟩))
  · -- 1, 0
    dsimp [basisBivector]
    have H : (ι Q (gamma Q 0) * ι Q (gamma Q 2)) * (ι Q (gamma Q 0) * ι Q (gamma Q 1)) - (ι Q (gamma Q 0) * ι Q (gamma Q 1)) * (ι Q (gamma Q 0) * ι Q (gamma Q 2)) = (- 2 : R) • (algebraMap R _ (Q (gamma Q 0)) * (ι Q (gamma Q 2) * ι Q (gamma Q 1))) := by
      calc (ι Q (gamma Q 0) * ι Q (gamma Q 2)) * (ι Q (gamma Q 0) * ι Q (gamma Q 1)) - (ι Q (gamma Q 0) * ι Q (gamma Q 1)) * (ι Q (gamma Q 0) * ι Q (gamma Q 2))
        _ = ι Q (gamma Q 0) * (ι Q (gamma Q 2) * ι Q (gamma Q 0)) * ι Q (gamma Q 1) - ι Q (gamma Q 0) * (ι Q (gamma Q 1) * ι Q (gamma Q 0)) * ι Q (gamma Q 2) := by simp only [mul_assoc, ←mul_assoc]
        _ = ι Q (gamma Q 0) * - (ι Q (gamma Q 0) * ι Q (gamma Q 2)) * ι Q (gamma Q 1) - ι Q (gamma Q 0) * - (ι Q (gamma Q 0) * ι Q (gamma Q 1)) * ι Q (gamma Q 2) := by rw [h20, h10]
        _ = - ((ι Q (gamma Q 0) * ι Q (gamma Q 0)) * (ι Q (gamma Q 2) * ι Q (gamma Q 1))) + (ι Q (gamma Q 0) * ι Q (gamma Q 0)) * (ι Q (gamma Q 1) * ι Q (gamma Q 2)) := by simp only [mul_neg, neg_mul, sub_neg_eq_add, ←mul_assoc, mul_assoc]
        _ = - (algebraMap R _ (Q (gamma Q 0)) * (ι Q (gamma Q 2) * ι Q (gamma Q 1))) + algebraMap R _ (Q (gamma Q 0)) * (ι Q (gamma Q 1) * ι Q (gamma Q 2)) := by rw [sq0]
        _ = - (algebraMap R _ (Q (gamma Q 0)) * (ι Q (gamma Q 2) * ι Q (gamma Q 1))) + algebraMap R _ (Q (gamma Q 0)) * - (ι Q (gamma Q 2) * ι Q (gamma Q 1)) := by rw [h21]
        _ = - (algebraMap R _ (Q (gamma Q 0)) * (ι Q (gamma Q 2) * ι Q (gamma Q 1))) - algebraMap R _ (Q (gamma Q 0)) * (ι Q (gamma Q 2) * ι Q (gamma Q 1)) := by simp only [mul_neg, neg_mul, sub_eq_add_neg, ←mul_assoc, mul_assoc]
        _ = (- 2 : R) • (algebraMap R _ (Q (gamma Q 0)) * (ι Q (gamma Q 2) * ι Q (gamma Q 1))) := by simp only [neg_sub_neg, smul_eq_mul, neg_smul]; ring
    have H2 : ι Q (gamma Q 2) * ι Q (gamma Q 1) = - basisBivector Q 5 := by rw [←h21]; rfl
    rw [H, H2]; simp only [mul_neg]; exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨5, rfl⟩))
  · -- 1, 1
    dsimp [basisBivector]
    have H : ι Q (gamma Q 0) * ι Q (gamma Q 2) * (ι Q (gamma Q 0) * ι Q (gamma Q 2)) - ι Q (gamma Q 0) * ι Q (gamma Q 2) * (ι Q (gamma Q 0) * ι Q (gamma Q 2)) = 0 := by rw [sub_self]
    rw [H]; exact Submodule.zero_mem _
  · -- 1, 2
    dsimp [basisBivector]
    have H : (ι Q (gamma Q 0) * ι Q (gamma Q 2)) * (ι Q (gamma Q 0) * ι Q (gamma Q 3)) - (ι Q (gamma Q 0) * ι Q (gamma Q 3)) * (ι Q (gamma Q 0) * ι Q (gamma Q 2)) = (- 2 : R) • (algebraMap R _ (Q (gamma Q 0)) * (ι Q (gamma Q 2) * ι Q (gamma Q 3))) := by
      calc (ι Q (gamma Q 0) * ι Q (gamma Q 2)) * (ι Q (gamma Q 0) * ι Q (gamma Q 3)) - (ι Q (gamma Q 0) * ι Q (gamma Q 3)) * (ι Q (gamma Q 0) * ι Q (gamma Q 2))
        _ = ι Q (gamma Q 0) * (ι Q (gamma Q 2) * ι Q (gamma Q 0)) * ι Q (gamma Q 3) - ι Q (gamma Q 0) * (ι Q (gamma Q 3) * ι Q (gamma Q 0)) * ι Q (gamma Q 2) := by simp only [mul_assoc, ←mul_assoc]
        _ = ι Q (gamma Q 0) * - (ι Q (gamma Q 0) * ι Q (gamma Q 2)) * ι Q (gamma Q 3) - ι Q (gamma Q 0) * - (ι Q (gamma Q 0) * ι Q (gamma Q 3)) * ι Q (gamma Q 2) := by rw [h20, h30]
        _ = - ((ι Q (gamma Q 0) * ι Q (gamma Q 0)) * (ι Q (gamma Q 2) * ι Q (gamma Q 3))) + (ι Q (gamma Q 0) * ι Q (gamma Q 0)) * (ι Q (gamma Q 3) * ι Q (gamma Q 2)) := by simp only [mul_neg, neg_mul, sub_neg_eq_add, ←mul_assoc, mul_assoc]
        _ = - (algebraMap R _ (Q (gamma Q 0)) * (ι Q (gamma Q 2) * ι Q (gamma Q 3))) + algebraMap R _ (Q (gamma Q 0)) * (ι Q (gamma Q 3) * ι Q (gamma Q 2)) := by rw [sq0]
        _ = - (algebraMap R _ (Q (gamma Q 0)) * (ι Q (gamma Q 2) * ι Q (gamma Q 3))) + algebraMap R _ (Q (gamma Q 0)) * - (ι Q (gamma Q 2) * ι Q (gamma Q 3)) := by rw [h32]
        _ = - (algebraMap R _ (Q (gamma Q 0)) * (ι Q (gamma Q 2) * ι Q (gamma Q 3))) - algebraMap R _ (Q (gamma Q 0)) * (ι Q (gamma Q 2) * ι Q (gamma Q 3)) := by simp only [mul_neg, neg_mul, sub_eq_add_neg, ←mul_assoc, mul_assoc]
        _ = (- 2 : R) • (algebraMap R _ (Q (gamma Q 0)) * (ι Q (gamma Q 2) * ι Q (gamma Q 3))) := by simp only [neg_sub_neg, smul_eq_mul, neg_smul]; ring
    have H2 : ι Q (gamma Q 2) * ι Q (gamma Q 3) = basisBivector Q 3 := rfl
    rw [H, H2]; exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨3, rfl⟩))
  · -- 1, 3
    dsimp [basisBivector]
    have H : (ι Q (gamma Q 0) * ι Q (gamma Q 2)) * (ι Q (gamma Q 2) * ι Q (gamma Q 3)) - (ι Q (gamma Q 2) * ι Q (gamma Q 3)) * (ι Q (gamma Q 0) * ι Q (gamma Q 2)) = (2 : R) • (algebraMap R _ (Q (gamma Q 2)) * (ι Q (gamma Q 0) * ι Q (gamma Q 3))) := by
      calc (ι Q (gamma Q 0) * ι Q (gamma Q 2)) * (ι Q (gamma Q 2) * ι Q (gamma Q 3)) - (ι Q (gamma Q 2) * ι Q (gamma Q 3)) * (ι Q (gamma Q 0) * ι Q (gamma Q 2))
        _ = ι Q (gamma Q 0) * (ι Q (gamma Q 2) * ι Q (gamma Q 2)) * ι Q (gamma Q 3) - ι Q (gamma Q 2) * (ι Q (gamma Q 3) * ι Q (gamma Q 0)) * ι Q (gamma Q 2) := by simp only [mul_assoc, ←mul_assoc]
        _ = ι Q (gamma Q 0) * algebraMap R _ (Q (gamma Q 2)) * ι Q (gamma Q 3) - ι Q (gamma Q 2) * (ι Q (gamma Q 3) * ι Q (gamma Q 0)) * ι Q (gamma Q 2) := by rw [sq2]
        _ = algebraMap R _ (Q (gamma Q 2)) * (ι Q (gamma Q 0) * ι Q (gamma Q 3)) - ι Q (gamma Q 2) * - (ι Q (gamma Q 0) * ι Q (gamma Q 3)) * ι Q (gamma Q 2) := by rw [h30, Algebra.commutes]
        _ = algebraMap R _ (Q (gamma Q 2)) * (ι Q (gamma Q 0) * ι Q (gamma Q 3)) + (ι Q (gamma Q 2) * ι Q (gamma Q 0)) * ι Q (gamma Q 3) * ι Q (gamma Q 2) := by simp only [mul_neg, neg_mul, sub_neg_eq_add, ←mul_assoc, mul_assoc]
        _ = algebraMap R _ (Q (gamma Q 2)) * (ι Q (gamma Q 0) * ι Q (gamma Q 3)) + - (ι Q (gamma Q 0) * ι Q (gamma Q 2)) * ι Q (gamma Q 3) * ι Q (gamma Q 2) := by rw [h20]
        _ = algebraMap R _ (Q (gamma Q 2)) * (ι Q (gamma Q 0) * ι Q (gamma Q 3)) - ι Q (gamma Q 0) * (ι Q (gamma Q 2) * ι Q (gamma Q 3)) * ι Q (gamma Q 2) := by simp only [mul_neg, neg_mul, ←mul_assoc, mul_assoc, sub_eq_add_neg, neg_neg]
        _ = algebraMap R _ (Q (gamma Q 2)) * (ι Q (gamma Q 0) * ι Q (gamma Q 3)) - ι Q (gamma Q 0) * - (ι Q (gamma Q 3) * ι Q (gamma Q 2)) * ι Q (gamma Q 2) := by rw [h32]
        _ = algebraMap R _ (Q (gamma Q 2)) * (ι Q (gamma Q 0) * ι Q (gamma Q 3)) + ι Q (gamma Q 0) * ι Q (gamma Q 3) * (ι Q (gamma Q 2) * ι Q (gamma Q 2)) := by simp only [mul_neg, neg_mul, sub_neg_eq_add, ←mul_assoc, mul_assoc]
        _ = algebraMap R _ (Q (gamma Q 2)) * (ι Q (gamma Q 0) * ι Q (gamma Q 3)) + ι Q (gamma Q 0) * ι Q (gamma Q 3) * algebraMap R _ (Q (gamma Q 2)) := by rw [sq2]
        _ = algebraMap R _ (Q (gamma Q 2)) * (ι Q (gamma Q 0) * ι Q (gamma Q 3)) + algebraMap R _ (Q (gamma Q 2)) * (ι Q (gamma Q 0) * ι Q (gamma Q 3)) := by rw [Algebra.commutes (Q (gamma Q 2))]
        _ = (2 : R) • (algebraMap R _ (Q (gamma Q 2)) * (ι Q (gamma Q 0) * ι Q (gamma Q 3))) := by simp only [smul_eq_mul]; ring
    have H2 : ι Q (gamma Q 0) * ι Q (gamma Q 3) = basisBivector Q 2 := rfl
    rw [H, H2]; exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨2, rfl⟩))
  · -- 1, 4
    dsimp [basisBivector]
    have H : (ι Q (gamma Q 0) * ι Q (gamma Q 2)) * (ι Q (gamma Q 3) * ι Q (gamma Q 1)) - (ι Q (gamma Q 3) * ι Q (gamma Q 1)) * (ι Q (gamma Q 0) * ι Q (gamma Q 2)) = 0 := by
      calc (ι Q (gamma Q 0) * ι Q (gamma Q 2)) * (ι Q (gamma Q 3) * ι Q (gamma Q 1)) - (ι Q (gamma Q 3) * ι Q (gamma Q 1)) * (ι Q (gamma Q 0) * ι Q (gamma Q 2))
        _ = ι Q (gamma Q 0) * ι Q (gamma Q 2) * ι Q (gamma Q 3) * ι Q (gamma Q 1) - ι Q (gamma Q 3) * ι Q (gamma Q 1) * ι Q (gamma Q 0) * ι Q (gamma Q 2) := by simp only [mul_assoc]
        _ = ι Q (gamma Q 0) * ι Q (gamma Q 2) * ι Q (gamma Q 3) * ι Q (gamma Q 1) - ι Q (gamma Q 3) * (ι Q (gamma Q 1) * ι Q (gamma Q 0)) * ι Q (gamma Q 2) := by simp only [←mul_assoc, mul_assoc]
        _ = ι Q (gamma Q 0) * ι Q (gamma Q 2) * ι Q (gamma Q 3) * ι Q (gamma Q 1) - ι Q (gamma Q 3) * - (ι Q (gamma Q 0) * ι Q (gamma Q 1)) * ι Q (gamma Q 2) := by rw [h10]
        _ = ι Q (gamma Q 0) * ι Q (gamma Q 2) * ι Q (gamma Q 3) * ι Q (gamma Q 1) + (ι Q (gamma Q 3) * ι Q (gamma Q 0)) * ι Q (gamma Q 1) * ι Q (gamma Q 2) := by simp only [mul_neg, neg_mul, sub_neg_eq_add, ←mul_assoc, mul_assoc]
        _ = ι Q (gamma Q 0) * ι Q (gamma Q 2) * ι Q (gamma Q 3) * ι Q (gamma Q 1) + - (ι Q (gamma Q 0) * ι Q (gamma Q 3)) * ι Q (gamma Q 1) * ι Q (gamma Q 2) := by rw [h30]
        _ = ι Q (gamma Q 0) * ι Q (gamma Q 2) * ι Q (gamma Q 3) * ι Q (gamma Q 1) - ι Q (gamma Q 0) * ι Q (gamma Q 3) * (ι Q (gamma Q 1) * ι Q (gamma Q 2)) := by simp only [neg_mul, mul_neg, ←mul_assoc, mul_assoc, sub_eq_add_neg, neg_neg]
        _ = ι Q (gamma Q 0) * ι Q (gamma Q 2) * ι Q (gamma Q 3) * ι Q (gamma Q 1) - ι Q (gamma Q 0) * ι Q (gamma Q 3) * - (ι Q (gamma Q 2) * ι Q (gamma Q 1)) := by rw [h21]
        _ = ι Q (gamma Q 0) * ι Q (gamma Q 2) * ι Q (gamma Q 3) * ι Q (gamma Q 1) + ι Q (gamma Q 0) * (ι Q (gamma Q 3) * ι Q (gamma Q 2)) * ι Q (gamma Q 1) := by simp only [mul_neg, neg_mul, sub_neg_eq_add, ←mul_assoc, mul_assoc]
        _ = ι Q (gamma Q 0) * ι Q (gamma Q 2) * ι Q (gamma Q 3) * ι Q (gamma Q 1) + ι Q (gamma Q 0) * - (ι Q (gamma Q 2) * ι Q (gamma Q 3)) * ι Q (gamma Q 1) := by rw [h32]
        _ = ι Q (gamma Q 0) * ι Q (gamma Q 2) * ι Q (gamma Q 3) * ι Q (gamma Q 1) - ι Q (gamma Q 0) * ι Q (gamma Q 2) * ι Q (gamma Q 3) * ι Q (gamma Q 1) := by simp only [mul_neg, neg_mul, sub_eq_add_neg, ←mul_assoc, mul_assoc]
        _ = 0 := by rw [sub_self]
    rw [H]; exact Submodule.zero_mem _
  · -- 1, 5
    dsimp [basisBivector]
    have H : (ι Q (gamma Q 0) * ι Q (gamma Q 2)) * (ι Q (gamma Q 1) * ι Q (gamma Q 2)) - (ι Q (gamma Q 1) * ι Q (gamma Q 2)) * (ι Q (gamma Q 0) * ι Q (gamma Q 2)) = (- 2 : R) • (algebraMap R _ (Q (gamma Q 2)) * (ι Q (gamma Q 0) * ι Q (gamma Q 1))) := by
      calc (ι Q (gamma Q 0) * ι Q (gamma Q 2)) * (ι Q (gamma Q 1) * ι Q (gamma Q 2)) - (ι Q (gamma Q 1) * ι Q (gamma Q 2)) * (ι Q (gamma Q 0) * ι Q (gamma Q 2))
        _ = ι Q (gamma Q 0) * (ι Q (gamma Q 2) * ι Q (gamma Q 1)) * ι Q (gamma Q 2) - ι Q (gamma Q 1) * (ι Q (gamma Q 2) * ι Q (gamma Q 0)) * ι Q (gamma Q 2) := by simp only [mul_assoc, ←mul_assoc]
        _ = ι Q (gamma Q 0) * - (ι Q (gamma Q 1) * ι Q (gamma Q 2)) * ι Q (gamma Q 2) - ι Q (gamma Q 1) * - (ι Q (gamma Q 0) * ι Q (gamma Q 2)) * ι Q (gamma Q 2) := by rw [h21, h20]
        _ = - (ι Q (gamma Q 0) * ι Q (gamma Q 1) * (ι Q (gamma Q 2) * ι Q (gamma Q 2))) + ι Q (gamma Q 1) * ι Q (gamma Q 0) * (ι Q (gamma Q 2) * ι Q (gamma Q 2)) := by simp only [mul_neg, neg_mul, sub_neg_eq_add, ←mul_assoc, mul_assoc]
        _ = - (ι Q (gamma Q 0) * ι Q (gamma Q 1) * algebraMap R _ (Q (gamma Q 2))) + (ι Q (gamma Q 1) * ι Q (gamma Q 0)) * algebraMap R _ (Q (gamma Q 2)) := by rw [sq2]
        _ = - (algebraMap R _ (Q (gamma Q 2)) * (ι Q (gamma Q 0) * ι Q (gamma Q 1))) + algebraMap R _ (Q (gamma Q 2)) * (ι Q (gamma Q 1) * ι Q (gamma Q 0)) := by rw [Algebra.commutes, Algebra.commutes (Q (gamma Q 2))]
        _ = - (algebraMap R _ (Q (gamma Q 2)) * (ι Q (gamma Q 0) * ι Q (gamma Q 1))) + algebraMap R _ (Q (gamma Q 2)) * - (ι Q (gamma Q 0) * ι Q (gamma Q 1)) := by rw [h10]
        _ = - (algebraMap R _ (Q (gamma Q 2)) * (ι Q (gamma Q 0) * ι Q (gamma Q 1))) - algebraMap R _ (Q (gamma Q 2)) * (ι Q (gamma Q 0) * ι Q (gamma Q 1)) := by simp only [mul_neg, neg_mul, sub_eq_add_neg, ←mul_assoc, mul_assoc]
        _ = (- 2 : R) • (algebraMap R _ (Q (gamma Q 2)) * (ι Q (gamma Q 0) * ι Q (gamma Q 1))) := by simp only [neg_sub_neg, smul_eq_mul, neg_smul]; ring
    have H2 : ι Q (gamma Q 0) * ι Q (gamma Q 1) = basisBivector Q 0 := rfl
    rw [H, H2]; exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩))
  · -- 2, 0
    dsimp [basisBivector]
    have H : (ι Q (gamma Q 0) * ι Q (gamma Q 3)) * (ι Q (gamma Q 0) * ι Q (gamma Q 1)) - (ι Q (gamma Q 0) * ι Q (gamma Q 1)) * (ι Q (gamma Q 0) * ι Q (gamma Q 3)) = (- 2 : R) • (algebraMap R _ (Q (gamma Q 0)) * (ι Q (gamma Q 3) * ι Q (gamma Q 1))) := by
      calc (ι Q (gamma Q 0) * ι Q (gamma Q 3)) * (ι Q (gamma Q 0) * ι Q (gamma Q 1)) - (ι Q (gamma Q 0) * ι Q (gamma Q 1)) * (ι Q (gamma Q 0) * ι Q (gamma Q 3))
        _ = ι Q (gamma Q 0) * (ι Q (gamma Q 3) * ι Q (gamma Q 0)) * ι Q (gamma Q 1) - ι Q (gamma Q 0) * (ι Q (gamma Q 1) * ι Q (gamma Q 0)) * ι Q (gamma Q 3) := by simp only [mul_assoc, ←mul_assoc]
        _ = ι Q (gamma Q 0) * - (ι Q (gamma Q 0) * ι Q (gamma Q 3)) * ι Q (gamma Q 1) - ι Q (gamma Q 0) * - (ι Q (gamma Q 0) * ι Q (gamma Q 1)) * ι Q (gamma Q 3) := by rw [h30, h10]
        _ = - ((ι Q (gamma Q 0) * ι Q (gamma Q 0)) * (ι Q (gamma Q 3) * ι Q (gamma Q 1))) + (ι Q (gamma Q 0) * ι Q (gamma Q 0)) * (ι Q (gamma Q 1) * ι Q (gamma Q 3)) := by simp only [mul_neg, neg_mul, sub_neg_eq_add, ←mul_assoc, mul_assoc]
        _ = - (algebraMap R _ (Q (gamma Q 0)) * (ι Q (gamma Q 3) * ι Q (gamma Q 1))) + algebraMap R _ (Q (gamma Q 0)) * (ι Q (gamma Q 1) * ι Q (gamma Q 3)) := by rw [sq0]
        _ = - (algebraMap R _ (Q (gamma Q 0)) * (ι Q (gamma Q 3) * ι Q (gamma Q 1))) + algebraMap R _ (Q (gamma Q 0)) * - (ι Q (gamma Q 3) * ι Q (gamma Q 1)) := by rw [h31]
        _ = - (algebraMap R _ (Q (gamma Q 0)) * (ι Q (gamma Q 3) * ι Q (gamma Q 1))) - algebraMap R _ (Q (gamma Q 0)) * (ι Q (gamma Q 3) * ι Q (gamma Q 1)) := by simp only [mul_neg, neg_mul, sub_eq_add_neg, ←mul_assoc, mul_assoc]
        _ = (- 2 : R) • (algebraMap R _ (Q (gamma Q 0)) * (ι Q (gamma Q 3) * ι Q (gamma Q 1))) := by simp only [neg_sub_neg, smul_eq_mul, neg_smul]; ring
    have H2 : ι Q (gamma Q 3) * ι Q (gamma Q 1) = basisBivector Q 4 := rfl
    rw [H, H2]; exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨4, rfl⟩))
  · -- 2, 1
    dsimp [basisBivector]
    have H : (ι Q (gamma Q 0) * ι Q (gamma Q 3)) * (ι Q (gamma Q 0) * ι Q (gamma Q 2)) - (ι Q (gamma Q 0) * ι Q (gamma Q 2)) * (ι Q (gamma Q 0) * ι Q (gamma Q 3)) = (- 2 : R) • (algebraMap R _ (Q (gamma Q 0)) * (ι Q (gamma Q 3) * ι Q (gamma Q 2))) := by
      calc (ι Q (gamma Q 0) * ι Q (gamma Q 3)) * (ι Q (gamma Q 0) * ι Q (gamma Q 2)) - (ι Q (gamma Q 0) * ι Q (gamma Q 2)) * (ι Q (gamma Q 0) * ι Q (gamma Q 3))
        _ = ι Q (gamma Q 0) * (ι Q (gamma Q 3) * ι Q (gamma Q 0)) * ι Q (gamma Q 2) - ι Q (gamma Q 0) * (ι Q (gamma Q 2) * ι Q (gamma Q 0)) * ι Q (gamma Q 3) := by simp only [mul_assoc, ←mul_assoc]
        _ = ι Q (gamma Q 0) * - (ι Q (gamma Q 0) * ι Q (gamma Q 3)) * ι Q (gamma Q 2) - ι Q (gamma Q 0) * - (ι Q (gamma Q 0) * ι Q (gamma Q 2)) * ι Q (gamma Q 3) := by rw [h30, h20]
        _ = - ((ι Q (gamma Q 0) * ι Q (gamma Q 0)) * (ι Q (gamma Q 3) * ι Q (gamma Q 2))) + (ι Q (gamma Q 0) * ι Q (gamma Q 0)) * (ι Q (gamma Q 2) * ι Q (gamma Q 3)) := by simp only [mul_neg, neg_mul, sub_neg_eq_add, ←mul_assoc, mul_assoc]
        _ = - (algebraMap R _ (Q (gamma Q 0)) * (ι Q (gamma Q 3) * ι Q (gamma Q 2))) + algebraMap R _ (Q (gamma Q 0)) * (ι Q (gamma Q 2) * ι Q (gamma Q 3)) := by rw [sq0]
        _ = - (algebraMap R _ (Q (gamma Q 0)) * (ι Q (gamma Q 3) * ι Q (gamma Q 2))) + algebraMap R _ (Q (gamma Q 0)) * - (ι Q (gamma Q 3) * ι Q (gamma Q 2)) := by rw [h32]
        _ = - (algebraMap R _ (Q (gamma Q 0)) * (ι Q (gamma Q 3) * ι Q (gamma Q 2))) - algebraMap R _ (Q (gamma Q 0)) * (ι Q (gamma Q 3) * ι Q (gamma Q 2)) := by simp only [mul_neg, neg_mul, sub_eq_add_neg, ←mul_assoc, mul_assoc]
        _ = (- 2 : R) • (algebraMap R _ (Q (gamma Q 0)) * (ι Q (gamma Q 3) * ι Q (gamma Q 2))) := by simp only [neg_sub_neg, smul_eq_mul, neg_smul]; ring
    have H2 : ι Q (gamma Q 3) * ι Q (gamma Q 2) = - basisBivector Q 3 := by rw [←h32]; rfl
    rw [H, H2]; simp only [mul_neg]; exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨3, rfl⟩))
  · -- 2, 2
    dsimp [basisBivector]
    have H : ι Q (gamma Q 0) * ι Q (gamma Q 3) * (ι Q (gamma Q 0) * ι Q (gamma Q 3)) - ι Q (gamma Q 0) * ι Q (gamma Q 3) * (ι Q (gamma Q 0) * ι Q (gamma Q 3)) = 0 := by rw [sub_self]
    rw [H]; exact Submodule.zero_mem _
  · -- 2, 3
    dsimp [basisBivector]
    have H : (ι Q (gamma Q 0) * ι Q (gamma Q 3)) * (ι Q (gamma Q 2) * ι Q (gamma Q 3)) - (ι Q (gamma Q 2) * ι Q (gamma Q 3)) * (ι Q (gamma Q 0) * ι Q (gamma Q 3)) = (- 2 : R) • (algebraMap R _ (Q (gamma Q 3)) * (ι Q (gamma Q 0) * ι Q (gamma Q 2))) := by
      calc (ι Q (gamma Q 0) * ι Q (gamma Q 3)) * (ι Q (gamma Q 2) * ι Q (gamma Q 3)) - (ι Q (gamma Q 2) * ι Q (gamma Q 3)) * (ι Q (gamma Q 0) * ι Q (gamma Q 3))
        _ = ι Q (gamma Q 0) * (ι Q (gamma Q 3) * ι Q (gamma Q 2)) * ι Q (gamma Q 3) - ι Q (gamma Q 2) * (ι Q (gamma Q 3) * ι Q (gamma Q 0)) * ι Q (gamma Q 3) := by simp only [mul_assoc, ←mul_assoc]
        _ = ι Q (gamma Q 0) * - (ι Q (gamma Q 2) * ι Q (gamma Q 3)) * ι Q (gamma Q 3) - ι Q (gamma Q 2) * - (ι Q (gamma Q 0) * ι Q (gamma Q 3)) * ι Q (gamma Q 3) := by rw [h32, h30]
        _ = - (ι Q (gamma Q 0) * ι Q (gamma Q 2) * (ι Q (gamma Q 3) * ι Q (gamma Q 3))) + ι Q (gamma Q 2) * ι Q (gamma Q 0) * (ι Q (gamma Q 3) * ι Q (gamma Q 3)) := by simp only [mul_neg, neg_mul, sub_neg_eq_add, ←mul_assoc, mul_assoc]
        _ = - (ι Q (gamma Q 0) * ι Q (gamma Q 2) * algebraMap R _ (Q (gamma Q 3))) + (ι Q (gamma Q 2) * ι Q (gamma Q 0)) * algebraMap R _ (Q (gamma Q 3)) := by rw [sq3]
        _ = - (algebraMap R _ (Q (gamma Q 3)) * (ι Q (gamma Q 0) * ι Q (gamma Q 2))) + algebraMap R _ (Q (gamma Q 3)) * (ι Q (gamma Q 2) * ι Q (gamma Q 0)) := by rw [Algebra.commutes, Algebra.commutes (Q (gamma Q 3))]
        _ = - (algebraMap R _ (Q (gamma Q 3)) * (ι Q (gamma Q 0) * ι Q (gamma Q 2))) + algebraMap R _ (Q (gamma Q 3)) * - (ι Q (gamma Q 0) * ι Q (gamma Q 2)) := by rw [h20]
        _ = - (algebraMap R _ (Q (gamma Q 3)) * (ι Q (gamma Q 0) * ι Q (gamma Q 2))) - algebraMap R _ (Q (gamma Q 3)) * (ι Q (gamma Q 0) * ι Q (gamma Q 2)) := by simp only [mul_neg, neg_mul, sub_eq_add_neg, ←mul_assoc, mul_assoc]
        _ = (- 2 : R) • (algebraMap R _ (Q (gamma Q 3)) * (ι Q (gamma Q 0) * ι Q (gamma Q 2))) := by simp only [neg_sub_neg, smul_eq_mul, neg_smul]; ring
    have H2 : ι Q (gamma Q 0) * ι Q (gamma Q 2) = basisBivector Q 1 := rfl
    rw [H, H2]; exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, rfl⟩))
  · -- 2, 4
    dsimp [basisBivector]
    have H : (ι Q (gamma Q 0) * ι Q (gamma Q 3)) * (ι Q (gamma Q 3) * ι Q (gamma Q 1)) - (ι Q (gamma Q 3) * ι Q (gamma Q 1)) * (ι Q (gamma Q 0) * ι Q (gamma Q 3)) = (2 : R) • (algebraMap R _ (Q (gamma Q 3)) * (ι Q (gamma Q 0) * ι Q (gamma Q 1))) := by
      calc (ι Q (gamma Q 0) * ι Q (gamma Q 3)) * (ι Q (gamma Q 3) * ι Q (gamma Q 1)) - (ι Q (gamma Q 3) * ι Q (gamma Q 1)) * (ι Q (gamma Q 0) * ι Q (gamma Q 3))
        _ = ι Q (gamma Q 0) * (ι Q (gamma Q 3) * ι Q (gamma Q 3)) * ι Q (gamma Q 1) - ι Q (gamma Q 3) * (ι Q (gamma Q 1) * ι Q (gamma Q 0)) * ι Q (gamma Q 3) := by simp only [mul_assoc, ←mul_assoc]
        _ = ι Q (gamma Q 0) * algebraMap R _ (Q (gamma Q 3)) * ι Q (gamma Q 1) - ι Q (gamma Q 3) * (ι Q (gamma Q 1) * ι Q (gamma Q 0)) * ι Q (gamma Q 3) := by rw [sq3]
        _ = algebraMap R _ (Q (gamma Q 3)) * (ι Q (gamma Q 0) * ι Q (gamma Q 1)) - ι Q (gamma Q 3) * - (ι Q (gamma Q 0) * ι Q (gamma Q 1)) * ι Q (gamma Q 3) := by rw [h10, Algebra.commutes]
        _ = algebraMap R _ (Q (gamma Q 3)) * (ι Q (gamma Q 0) * ι Q (gamma Q 1)) + (ι Q (gamma Q 3) * ι Q (gamma Q 0)) * ι Q (gamma Q 1) * ι Q (gamma Q 3) := by simp only [mul_neg, neg_mul, sub_neg_eq_add, ←mul_assoc, mul_assoc]
        _ = algebraMap R _ (Q (gamma Q 3)) * (ι Q (gamma Q 0) * ι Q (gamma Q 1)) + - (ι Q (gamma Q 0) * ι Q (gamma Q 3)) * ι Q (gamma Q 1) * ι Q (gamma Q 3) := by rw [h30]
        _ = algebraMap R _ (Q (gamma Q 3)) * (ι Q (gamma Q 0) * ι Q (gamma Q 1)) - ι Q (gamma Q 0) * (ι Q (gamma Q 3) * ι Q (gamma Q 1)) * ι Q (gamma Q 3) := by simp only [mul_neg, neg_mul, ←mul_assoc, mul_assoc, sub_eq_add_neg, neg_neg]
        _ = algebraMap R _ (Q (gamma Q 3)) * (ι Q (gamma Q 0) * ι Q (gamma Q 1)) - ι Q (gamma Q 0) * - (ι Q (gamma Q 1) * ι Q (gamma Q 3)) * ι Q (gamma Q 3) := by rw [h31]
        _ = algebraMap R _ (Q (gamma Q 3)) * (ι Q (gamma Q 0) * ι Q (gamma Q 1)) + ι Q (gamma Q 0) * ι Q (gamma Q 1) * (ι Q (gamma Q 3) * ι Q (gamma Q 3)) := by simp only [mul_neg, neg_mul, sub_neg_eq_add, ←mul_assoc, mul_assoc]
        _ = algebraMap R _ (Q (gamma Q 3)) * (ι Q (gamma Q 0) * ι Q (gamma Q 1)) + ι Q (gamma Q 0) * ι Q (gamma Q 1) * algebraMap R _ (Q (gamma Q 3)) := by rw [sq3]
        _ = algebraMap R _ (Q (gamma Q 3)) * (ι Q (gamma Q 0) * ι Q (gamma Q 1)) + algebraMap R _ (Q (gamma Q 3)) * (ι Q (gamma Q 0) * ι Q (gamma Q 1)) := by rw [Algebra.commutes (Q (gamma Q 3))]
        _ = (2 : R) • (algebraMap R _ (Q (gamma Q 3)) * (ι Q (gamma Q 0) * ι Q (gamma Q 1))) := by simp only [smul_eq_mul]; ring
    have H2 : ι Q (gamma Q 0) * ι Q (gamma Q 1) = basisBivector Q 0 := rfl
    rw [H, H2]; exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩))
  · -- 2, 5
    dsimp [basisBivector]
    have H : (ι Q (gamma Q 0) * ι Q (gamma Q 3)) * (ι Q (gamma Q 1) * ι Q (gamma Q 2)) - (ι Q (gamma Q 1) * ι Q (gamma Q 2)) * (ι Q (gamma Q 0) * ι Q (gamma Q 3)) = 0 := by
      calc (ι Q (gamma Q 0) * ι Q (gamma Q 3)) * (ι Q (gamma Q 1) * ι Q (gamma Q 2)) - (ι Q (gamma Q 1) * ι Q (gamma Q 2)) * (ι Q (gamma Q 0) * ι Q (gamma Q 3))
        _ = ι Q (gamma Q 0) * ι Q (gamma Q 3) * ι Q (gamma Q 1) * ι Q (gamma Q 2) - ι Q (gamma Q 1) * ι Q (gamma Q 2) * ι Q (gamma Q 0) * ι Q (gamma Q 3) := by simp only [mul_assoc]
        _ = ι Q (gamma Q 0) * ι Q (gamma Q 3) * ι Q (gamma Q 1) * ι Q (gamma Q 2) - ι Q (gamma Q 1) * (ι Q (gamma Q 2) * ι Q (gamma Q 0)) * ι Q (gamma Q 3) := by simp only [←mul_assoc, mul_assoc]
        _ = ι Q (gamma Q 0) * ι Q (gamma Q 3) * ι Q (gamma Q 1) * ι Q (gamma Q 2) - ι Q (gamma Q 1) * - (ι Q (gamma Q 0) * ι Q (gamma Q 2)) * ι Q (gamma Q 3) := by rw [h20]
        _ = ι Q (gamma Q 0) * ι Q (gamma Q 3) * ι Q (gamma Q 1) * ι Q (gamma Q 2) + (ι Q (gamma Q 1) * ι Q (gamma Q 0)) * ι Q (gamma Q 2) * ι Q (gamma Q 3) := by simp only [mul_neg, neg_mul, sub_neg_eq_add, ←mul_assoc, mul_assoc]
        _ = ι Q (gamma Q 0) * ι Q (gamma Q 3) * ι Q (gamma Q 1) * ι Q (gamma Q 2) + - (ι Q (gamma Q 0) * ι Q (gamma Q 1)) * ι Q (gamma Q 2) * ι Q (gamma Q 3) := by rw [h10]
        _ = ι Q (gamma Q 0) * ι Q (gamma Q 3) * ι Q (gamma Q 1) * ι Q (gamma Q 2) - ι Q (gamma Q 0) * ι Q (gamma Q 1) * (ι Q (gamma Q 2) * ι Q (gamma Q 3)) := by simp only [neg_mul, mul_neg, ←mul_assoc, mul_assoc, sub_eq_add_neg, neg_neg]
        _ = ι Q (gamma Q 0) * ι Q (gamma Q 3) * ι Q (gamma Q 1) * ι Q (gamma Q 2) - ι Q (gamma Q 0) * ι Q (gamma Q 1) * - (ι Q (gamma Q 3) * ι Q (gamma Q 2)) := by rw [h32]
        _ = ι Q (gamma Q 0) * ι Q (gamma Q 3) * ι Q (gamma Q 1) * ι Q (gamma Q 2) + ι Q (gamma Q 0) * (ι Q (gamma Q 1) * ι Q (gamma Q 3)) * ι Q (gamma Q 2) := by simp only [mul_neg, neg_mul, sub_neg_eq_add, ←mul_assoc, mul_assoc]
        _ = ι Q (gamma Q 0) * ι Q (gamma Q 3) * ι Q (gamma Q 1) * ι Q (gamma Q 2) + ι Q (gamma Q 0) * - (ι Q (gamma Q 3) * ι Q (gamma Q 1)) * ι Q (gamma Q 2) := by rw [h31]
        _ = ι Q (gamma Q 0) * ι Q (gamma Q 3) * ι Q (gamma Q 1) * ι Q (gamma Q 2) - ι Q (gamma Q 0) * ι Q (gamma Q 3) * ι Q (gamma Q 1) * ι Q (gamma Q 2) := by simp only [mul_neg, neg_mul, sub_eq_add_neg, ←mul_assoc, mul_assoc]
        _ = 0 := by rw [sub_self]
    rw [H]; exact Submodule.zero_mem _
  · -- 3, 0
    dsimp [basisBivector]
    have H : (ι Q (gamma Q 2) * ι Q (gamma Q 3)) * (ι Q (gamma Q 0) * ι Q (gamma Q 1)) - (ι Q (gamma Q 0) * ι Q (gamma Q 1)) * (ι Q (gamma Q 2) * ι Q (gamma Q 3)) = 0 := by
      calc (ι Q (gamma Q 2) * ι Q (gamma Q 3)) * (ι Q (gamma Q 0) * ι Q (gamma Q 1)) - (ι Q (gamma Q 0) * ι Q (gamma Q 1)) * (ι Q (gamma Q 2) * ι Q (gamma Q 3))
        _ = ι Q (gamma Q 2) * ι Q (gamma Q 3) * ι Q (gamma Q 0) * ι Q (gamma Q 1) - ι Q (gamma Q 0) * ι Q (gamma Q 1) * ι Q (gamma Q 2) * ι Q (gamma Q 3) := by simp only [mul_assoc]
        _ = ι Q (gamma Q 2) * ι Q (gamma Q 3) * ι Q (gamma Q 0) * ι Q (gamma Q 1) - ι Q (gamma Q 0) * (ι Q (gamma Q 1) * ι Q (gamma Q 2)) * ι Q (gamma Q 3) := by simp only [←mul_assoc, mul_assoc]
        _ = ι Q (gamma Q 2) * ι Q (gamma Q 3) * ι Q (gamma Q 0) * ι Q (gamma Q 1) - ι Q (gamma Q 0) * - (ι Q (gamma Q 2) * ι Q (gamma Q 1)) * ι Q (gamma Q 3) := by rw [h21]
        _ = ι Q (gamma Q 2) * ι Q (gamma Q 3) * ι Q (gamma Q 0) * ι Q (gamma Q 1) + (ι Q (gamma Q 0) * ι Q (gamma Q 2)) * ι Q (gamma Q 1) * ι Q (gamma Q 3) := by simp only [mul_neg, neg_mul, sub_neg_eq_add, ←mul_assoc, mul_assoc]
        _ = ι Q (gamma Q 2) * ι Q (gamma Q 3) * ι Q (gamma Q 0) * ι Q (gamma Q 1) + - (ι Q (gamma Q 2) * ι Q (gamma Q 0)) * ι Q (gamma Q 1) * ι Q (gamma Q 3) := by rw [h20]
        _ = ι Q (gamma Q 2) * ι Q (gamma Q 3) * ι Q (gamma Q 0) * ι Q (gamma Q 1) - ι Q (gamma Q 2) * ι Q (gamma Q 0) * (ι Q (gamma Q 1) * ι Q (gamma Q 3)) := by simp only [neg_mul, mul_neg, ←mul_assoc, mul_assoc, sub_eq_add_neg, neg_neg]
        _ = ι Q (gamma Q 2) * ι Q (gamma Q 3) * ι Q (gamma Q 0) * ι Q (gamma Q 1) - ι Q (gamma Q 2) * ι Q (gamma Q 0) * - (ι Q (gamma Q 3) * ι Q (gamma Q 1)) := by rw [h31]
        _ = ι Q (gamma Q 2) * ι Q (gamma Q 3) * ι Q (gamma Q 0) * ι Q (gamma Q 1) + ι Q (gamma Q 2) * (ι Q (gamma Q 0) * ι Q (gamma Q 3)) * ι Q (gamma Q 1) := by simp only [mul_neg, neg_mul, sub_neg_eq_add, ←mul_assoc, mul_assoc]
        _ = ι Q (gamma Q 2) * ι Q (gamma Q 3) * ι Q (gamma Q 0) * ι Q (gamma Q 1) + ι Q (gamma Q 2) * - (ι Q (gamma Q 3) * ι Q (gamma Q 0)) * ι Q (gamma Q 1) := by rw [h30]
        _ = ι Q (gamma Q 2) * ι Q (gamma Q 3) * ι Q (gamma Q 0) * ι Q (gamma Q 1) - ι Q (gamma Q 2) * ι Q (gamma Q 3) * ι Q (gamma Q 0) * ι Q (gamma Q 1) := by simp only [mul_neg, neg_mul, sub_eq_add_neg, ←mul_assoc, mul_assoc]
        _ = 0 := by rw [sub_self]
    rw [H]; exact Submodule.zero_mem _
  · -- 3, 1
    dsimp [basisBivector]
    have H : (ι Q (gamma Q 2) * ι Q (gamma Q 3)) * (ι Q (gamma Q 0) * ι Q (gamma Q 2)) - (ι Q (gamma Q 0) * ι Q (gamma Q 2)) * (ι Q (gamma Q 2) * ι Q (gamma Q 3)) = (2 : R) • (algebraMap R _ (Q (gamma Q 2)) * (ι Q (gamma Q 3) * ι Q (gamma Q 0))) := by
      calc (ι Q (gamma Q 2) * ι Q (gamma Q 3)) * (ι Q (gamma Q 0) * ι Q (gamma Q 2)) - (ι Q (gamma Q 0) * ι Q (gamma Q 2)) * (ι Q (gamma Q 2) * ι Q (gamma Q 3))
        _ = ι Q (gamma Q 2) * (ι Q (gamma Q 3) * ι Q (gamma Q 0)) * ι Q (gamma Q 2) - ι Q (gamma Q 0) * (ι Q (gamma Q 2) * ι Q (gamma Q 2)) * ι Q (gamma Q 3) := by simp only [mul_assoc, ←mul_assoc]
        _ = ι Q (gamma Q 2) * (ι Q (gamma Q 3) * ι Q (gamma Q 0)) * ι Q (gamma Q 2) - ι Q (gamma Q 0) * algebraMap R _ (Q (gamma Q 2)) * ι Q (gamma Q 3) := by rw [sq2]
        _ = ι Q (gamma Q 2) * - (ι Q (gamma Q 0) * ι Q (gamma Q 3)) * ι Q (gamma Q 2) - algebraMap R _ (Q (gamma Q 2)) * (ι Q (gamma Q 0) * ι Q (gamma Q 3)) := by rw [h30, Algebra.commutes]
        _ = - (ι Q (gamma Q 2) * ι Q (gamma Q 0) * ι Q (gamma Q 3) * ι Q (gamma Q 2)) - algebraMap R _ (Q (gamma Q 2)) * (ι Q (gamma Q 0) * ι Q (gamma Q 3)) := by simp only [mul_neg, neg_mul, ←mul_assoc, mul_assoc]
        _ = - (ι Q (gamma Q 2) * ι Q (gamma Q 0) * (ι Q (gamma Q 3) * ι Q (gamma Q 2))) - algebraMap R _ (Q (gamma Q 2)) * (ι Q (gamma Q 0) * ι Q (gamma Q 3)) := by simp only [mul_assoc]
        _ = - (ι Q (gamma Q 2) * ι Q (gamma Q 0) * - (ι Q (gamma Q 2) * ι Q (gamma Q 3))) - algebraMap R _ (Q (gamma Q 2)) * (ι Q (gamma Q 0) * ι Q (gamma Q 3)) := by rw [h32]
        _ = ι Q (gamma Q 2) * (ι Q (gamma Q 0) * ι Q (gamma Q 2)) * ι Q (gamma Q 3) - algebraMap R _ (Q (gamma Q 2)) * (ι Q (gamma Q 0) * ι Q (gamma Q 3)) := by simp only [mul_neg, neg_mul, neg_neg, ←mul_assoc, mul_assoc]
        _ = ι Q (gamma Q 2) * - (ι Q (gamma Q 2) * ι Q (gamma Q 0)) * ι Q (gamma Q 3) - algebraMap R _ (Q (gamma Q 2)) * (ι Q (gamma Q 0) * ι Q (gamma Q 3)) := by rw [h20]
        _ = - ((ι Q (gamma Q 2) * ι Q (gamma Q 2)) * (ι Q (gamma Q 0) * ι Q (gamma Q 3))) - algebraMap R _ (Q (gamma Q 2)) * (ι Q (gamma Q 0) * ι Q (gamma Q 3)) := by simp only [mul_neg, neg_mul, ←mul_assoc, mul_assoc]
        _ = - (algebraMap R _ (Q (gamma Q 2)) * (ι Q (gamma Q 0) * ι Q (gamma Q 3))) - algebraMap R _ (Q (gamma Q 2)) * (ι Q (gamma Q 0) * ι Q (gamma Q 3)) := by rw [sq2]
        _ = - (algebraMap R _ (Q (gamma Q 2)) * - (ι Q (gamma Q 3) * ι Q (gamma Q 0))) - algebraMap R _ (Q (gamma Q 2)) * - (ι Q (gamma Q 3) * ι Q (gamma Q 0)) := by rw [h30]
        _ = algebraMap R _ (Q (gamma Q 2)) * (ι Q (gamma Q 3) * ι Q (gamma Q 0)) + algebraMap R _ (Q (gamma Q 2)) * (ι Q (gamma Q 3) * ι Q (gamma Q 0)) := by simp only [mul_neg, neg_mul, sub_eq_add_neg, neg_neg]
        _ = (2 : R) • (algebraMap R _ (Q (gamma Q 2)) * (ι Q (gamma Q 3) * ι Q (gamma Q 0))) := by simp only [smul_eq_mul]; ring
    have H2 : ι Q (gamma Q 3) * ι Q (gamma Q 0) = - basisBivector Q 2 := by rw [←h30]; rfl
    rw [H, H2]; simp only [mul_neg]; exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨2, rfl⟩))
  · -- 3, 2
    dsimp [basisBivector]
    have H : (ι Q (gamma Q 2) * ι Q (gamma Q 3)) * (ι Q (gamma Q 0) * ι Q (gamma Q 3)) - (ι Q (gamma Q 0) * ι Q (gamma Q 3)) * (ι Q (gamma Q 2) * ι Q (gamma Q 3)) = (- 2 : R) • (algebraMap R _ (Q (gamma Q 3)) * (ι Q (gamma Q 2) * ι Q (gamma Q 0))) := by
      calc (ι Q (gamma Q 2) * ι Q (gamma Q 3)) * (ι Q (gamma Q 0) * ι Q (gamma Q 3)) - (ι Q (gamma Q 0) * ι Q (gamma Q 3)) * (ι Q (gamma Q 2) * ι Q (gamma Q 3))
        _ = ι Q (gamma Q 2) * (ι Q (gamma Q 3) * ι Q (gamma Q 0)) * ι Q (gamma Q 3) - ι Q (gamma Q 0) * (ι Q (gamma Q 3) * ι Q (gamma Q 2)) * ι Q (gamma Q 3) := by simp only [mul_assoc, ←mul_assoc]
        _ = ι Q (gamma Q 2) * - (ι Q (gamma Q 0) * ι Q (gamma Q 3)) * ι Q (gamma Q 3) - ι Q (gamma Q 0) * - (ι Q (gamma Q 2) * ι Q (gamma Q 3)) * ι Q (gamma Q 3) := by rw [h30, h32]
        _ = - (ι Q (gamma Q 2) * ι Q (gamma Q 0) * (ι Q (gamma Q 3) * ι Q (gamma Q 3))) + ι Q (gamma Q 0) * ι Q (gamma Q 2) * (ι Q (gamma Q 3) * ι Q (gamma Q 3)) := by simp only [mul_neg, neg_mul, sub_neg_eq_add, ←mul_assoc, mul_assoc]
        _ = - (ι Q (gamma Q 2) * ι Q (gamma Q 0) * algebraMap R _ (Q (gamma Q 3))) + (ι Q (gamma Q 0) * ι Q (gamma Q 2)) * algebraMap R _ (Q (gamma Q 3)) := by rw [sq3]
        _ = - (algebraMap R _ (Q (gamma Q 3)) * (ι Q (gamma Q 2) * ι Q (gamma Q 0))) + algebraMap R _ (Q (gamma Q 3)) * (ι Q (gamma Q 0) * ι Q (gamma Q 2)) := by rw [Algebra.commutes, Algebra.commutes (Q (gamma Q 3))]
        _ = - (algebraMap R _ (Q (gamma Q 3)) * (ι Q (gamma Q 2) * ι Q (gamma Q 0))) + algebraMap R _ (Q (gamma Q 3)) * - (ι Q (gamma Q 2) * ι Q (gamma Q 0)) := by rw [h20]
        _ = - (algebraMap R _ (Q (gamma Q 3)) * (ι Q (gamma Q 2) * ι Q (gamma Q 0))) - algebraMap R _ (Q (gamma Q 3)) * (ι Q (gamma Q 2) * ι Q (gamma Q 0)) := by simp only [mul_neg, neg_mul, sub_eq_add_neg, ←mul_assoc, mul_assoc]
        _ = (- 2 : R) • (algebraMap R _ (Q (gamma Q 3)) * (ι Q (gamma Q 2) * ι Q (gamma Q 0))) := by simp only [neg_sub_neg, smul_eq_mul, neg_smul]; ring
    have H2 : ι Q (gamma Q 2) * ι Q (gamma Q 0) = - basisBivector Q 1 := by rw [←h20]; rfl
    rw [H, H2]; simp only [mul_neg]; exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, rfl⟩))
  · -- 3, 3
    dsimp [basisBivector]
    have H : ι Q (gamma Q 2) * ι Q (gamma Q 3) * (ι Q (gamma Q 2) * ι Q (gamma Q 3)) - ι Q (gamma Q 2) * ι Q (gamma Q 3) * (ι Q (gamma Q 2) * ι Q (gamma Q 3)) = 0 := by rw [sub_self]
    rw [H]; exact Submodule.zero_mem _
  · -- 3, 4
    dsimp [basisBivector]
    have H : (ι Q (gamma Q 2) * ι Q (gamma Q 3)) * (ι Q (gamma Q 3) * ι Q (gamma Q 1)) - (ι Q (gamma Q 3) * ι Q (gamma Q 1)) * (ι Q (gamma Q 2) * ι Q (gamma Q 3)) = (2 : R) • (algebraMap R _ (Q (gamma Q 3)) * (ι Q (gamma Q 2) * ι Q (gamma Q 1))) := by
      calc (ι Q (gamma Q 2) * ι Q (gamma Q 3)) * (ι Q (gamma Q 3) * ι Q (gamma Q 1)) - (ι Q (gamma Q 3) * ι Q (gamma Q 1)) * (ι Q (gamma Q 2) * ι Q (gamma Q 3))
        _ = ι Q (gamma Q 2) * (ι Q (gamma Q 3) * ι Q (gamma Q 3)) * ι Q (gamma Q 1) - ι Q (gamma Q 3) * (ι Q (gamma Q 1) * ι Q (gamma Q 2)) * ι Q (gamma Q 3) := by simp only [mul_assoc, ←mul_assoc]
        _ = ι Q (gamma Q 2) * algebraMap R _ (Q (gamma Q 3)) * ι Q (gamma Q 1) - ι Q (gamma Q 3) * (ι Q (gamma Q 1) * ι Q (gamma Q 2)) * ι Q (gamma Q 3) := by rw [sq3]
        _ = algebraMap R _ (Q (gamma Q 3)) * (ι Q (gamma Q 2) * ι Q (gamma Q 1)) - ι Q (gamma Q 3) * - (ι Q (gamma Q 2) * ι Q (gamma Q 1)) * ι Q (gamma Q 3) := by rw [h21, Algebra.commutes]
        _ = algebraMap R _ (Q (gamma Q 3)) * (ι Q (gamma Q 2) * ι Q (gamma Q 1)) + (ι Q (gamma Q 3) * ι Q (gamma Q 2)) * ι Q (gamma Q 1) * ι Q (gamma Q 3) := by simp only [mul_neg, neg_mul, sub_neg_eq_add, ←mul_assoc, mul_assoc]
        _ = algebraMap R _ (Q (gamma Q 3)) * (ι Q (gamma Q 2) * ι Q (gamma Q 1)) + - (ι Q (gamma Q 2) * ι Q (gamma Q 3)) * ι Q (gamma Q 1) * ι Q (gamma Q 3) := by rw [h32]
        _ = algebraMap R _ (Q (gamma Q 3)) * (ι Q (gamma Q 2) * ι Q (gamma Q 1)) - ι Q (gamma Q 2) * (ι Q (gamma Q 3) * ι Q (gamma Q 1)) * ι Q (gamma Q 3) := by simp only [mul_neg, neg_mul, ←mul_assoc, mul_assoc, sub_eq_add_neg, neg_neg]
        _ = algebraMap R _ (Q (gamma Q 3)) * (ι Q (gamma Q 2) * ι Q (gamma Q 1)) - ι Q (gamma Q 2) * - (ι Q (gamma Q 1) * ι Q (gamma Q 3)) * ι Q (gamma Q 3) := by rw [h31]
        _ = algebraMap R _ (Q (gamma Q 3)) * (ι Q (gamma Q 2) * ι Q (gamma Q 1)) + ι Q (gamma Q 2) * ι Q (gamma Q 1) * (ι Q (gamma Q 3) * ι Q (gamma Q 3)) := by simp only [mul_neg, neg_mul, sub_neg_eq_add, ←mul_assoc, mul_assoc]
        _ = algebraMap R _ (Q (gamma Q 3)) * (ι Q (gamma Q 2) * ι Q (gamma Q 1)) + ι Q (gamma Q 2) * ι Q (gamma Q 1) * algebraMap R _ (Q (gamma Q 3)) := by rw [sq3]
        _ = algebraMap R _ (Q (gamma Q 3)) * (ι Q (gamma Q 2) * ι Q (gamma Q 1)) + algebraMap R _ (Q (gamma Q 3)) * (ι Q (gamma Q 2) * ι Q (gamma Q 1)) := by rw [Algebra.commutes (Q (gamma Q 3))]
        _ = (2 : R) • (algebraMap R _ (Q (gamma Q 3)) * (ι Q (gamma Q 2) * ι Q (gamma Q 1))) := by simp only [smul_eq_mul]; ring
    have H2 : ι Q (gamma Q 2) * ι Q (gamma Q 1) = - basisBivector Q 5 := by rw [←h21]; rfl
    rw [H, H2]; simp only [mul_neg]; exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨5, rfl⟩))
  · -- 3, 5
    dsimp [basisBivector]
    have H : (ι Q (gamma Q 2) * ι Q (gamma Q 3)) * (ι Q (gamma Q 1) * ι Q (gamma Q 2)) - (ι Q (gamma Q 1) * ι Q (gamma Q 2)) * (ι Q (gamma Q 2) * ι Q (gamma Q 3)) = (2 : R) • (algebraMap R _ (Q (gamma Q 2)) * (ι Q (gamma Q 3) * ι Q (gamma Q 1))) := by
      calc (ι Q (gamma Q 2) * ι Q (gamma Q 3)) * (ι Q (gamma Q 1) * ι Q (gamma Q 2)) - (ι Q (gamma Q 1) * ι Q (gamma Q 2)) * (ι Q (gamma Q 2) * ι Q (gamma Q 3))
        _ = ι Q (gamma Q 2) * (ι Q (gamma Q 3) * ι Q (gamma Q 1)) * ι Q (gamma Q 2) - ι Q (gamma Q 1) * (ι Q (gamma Q 2) * ι Q (gamma Q 2)) * ι Q (gamma Q 3) := by simp only [mul_assoc, ←mul_assoc]
        _ = ι Q (gamma Q 2) * (ι Q (gamma Q 3) * ι Q (gamma Q 1)) * ι Q (gamma Q 2) - ι Q (gamma Q 1) * algebraMap R _ (Q (gamma Q 2)) * ι Q (gamma Q 3) := by rw [sq2]
        _ = ι Q (gamma Q 2) * - (ι Q (gamma Q 1) * ι Q (gamma Q 3)) * ι Q (gamma Q 2) - algebraMap R _ (Q (gamma Q 2)) * (ι Q (gamma Q 1) * ι Q (gamma Q 3)) := by rw [h31, Algebra.commutes]
        _ = - (ι Q (gamma Q 2) * ι Q (gamma Q 1) * ι Q (gamma Q 3) * ι Q (gamma Q 2)) - algebraMap R _ (Q (gamma Q 2)) * (ι Q (gamma Q 1) * ι Q (gamma Q 3)) := by simp only [mul_neg, neg_mul, ←mul_assoc, mul_assoc]
        _ = - (ι Q (gamma Q 2) * ι Q (gamma Q 1) * (ι Q (gamma Q 3) * ι Q (gamma Q 2))) - algebraMap R _ (Q (gamma Q 2)) * (ι Q (gamma Q 1) * ι Q (gamma Q 3)) := by simp only [mul_assoc]
        _ = - (ι Q (gamma Q 2) * ι Q (gamma Q 1) * - (ι Q (gamma Q 2) * ι Q (gamma Q 3))) - algebraMap R _ (Q (gamma Q 2)) * (ι Q (gamma Q 1) * ι Q (gamma Q 3)) := by rw [h32]
        _ = ι Q (gamma Q 2) * (ι Q (gamma Q 1) * ι Q (gamma Q 2)) * ι Q (gamma Q 3) - algebraMap R _ (Q (gamma Q 2)) * (ι Q (gamma Q 1) * ι Q (gamma Q 3)) := by simp only [mul_neg, neg_mul, neg_neg, ←mul_assoc, mul_assoc]
        _ = ι Q (gamma Q 2) * - (ι Q (gamma Q 2) * ι Q (gamma Q 1)) * ι Q (gamma Q 3) - algebraMap R _ (Q (gamma Q 2)) * (ι Q (gamma Q 1) * ι Q (gamma Q 3)) := by rw [h21]
        _ = - ((ι Q (gamma Q 2) * ι Q (gamma Q 2)) * (ι Q (gamma Q 1) * ι Q (gamma Q 3))) - algebraMap R _ (Q (gamma Q 2)) * (ι Q (gamma Q 1) * ι Q (gamma Q 3)) := by simp only [mul_neg, neg_mul, ←mul_assoc, mul_assoc]
        _ = - (algebraMap R _ (Q (gamma Q 2)) * (ι Q (gamma Q 1) * ι Q (gamma Q 3))) - algebraMap R _ (Q (gamma Q 2)) * (ι Q (gamma Q 1) * ι Q (gamma Q 3)) := by rw [sq2]
        _ = - (algebraMap R _ (Q (gamma Q 2)) * - (ι Q (gamma Q 3) * ι Q (gamma Q 1))) - algebraMap R _ (Q (gamma Q 2)) * - (ι Q (gamma Q 3) * ι Q (gamma Q 1)) := by rw [h31]
        _ = algebraMap R _ (Q (gamma Q 2)) * (ι Q (gamma Q 3) * ι Q (gamma Q 1)) + algebraMap R _ (Q (gamma Q 2)) * (ι Q (gamma Q 3) * ι Q (gamma Q 1)) := by simp only [mul_neg, neg_mul, sub_eq_add_neg, neg_neg]
        _ = (2 : R) • (algebraMap R _ (Q (gamma Q 2)) * (ι Q (gamma Q 3) * ι Q (gamma Q 1))) := by simp only [smul_eq_mul]; ring
    have H2 : ι Q (gamma Q 3) * ι Q (gamma Q 1) = basisBivector Q 4 := rfl
    rw [H, H2]; exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨4, rfl⟩))
  · -- 4, 0
    dsimp [basisBivector]
    have H : (ι Q (gamma Q 3) * ι Q (gamma Q 1)) * (ι Q (gamma Q 0) * ι Q (gamma Q 1)) - (ι Q (gamma Q 0) * ι Q (gamma Q 1)) * (ι Q (gamma Q 3) * ι Q (gamma Q 1)) = (- 2 : R) • (algebraMap R _ (Q (gamma Q 1)) * (ι Q (gamma Q 3) * ι Q (gamma Q 0))) := by
      calc (ι Q (gamma Q 3) * ι Q (gamma Q 1)) * (ι Q (gamma Q 0) * ι Q (gamma Q 1)) - (ι Q (gamma Q 0) * ι Q (gamma Q 1)) * (ι Q (gamma Q 3) * ι Q (gamma Q 1))
        _ = ι Q (gamma Q 3) * (ι Q (gamma Q 1) * ι Q (gamma Q 0)) * ι Q (gamma Q 1) - ι Q (gamma Q 0) * (ι Q (gamma Q 1) * ι Q (gamma Q 3)) * ι Q (gamma Q 1) := by simp only [mul_assoc, ←mul_assoc]
        _ = ι Q (gamma Q 3) * - (ι Q (gamma Q 0) * ι Q (gamma Q 1)) * ι Q (gamma Q 1) - ι Q (gamma Q 0) * - (ι Q (gamma Q 3) * ι Q (gamma Q 1)) * ι Q (gamma Q 1) := by rw [h10, h31]
        _ = - (ι Q (gamma Q 3) * ι Q (gamma Q 0) * (ι Q (gamma Q 1) * ι Q (gamma Q 1))) + ι Q (gamma Q 0) * ι Q (gamma Q 3) * (ι Q (gamma Q 1) * ι Q (gamma Q 1)) := by simp only [mul_neg, neg_mul, sub_neg_eq_add, ←mul_assoc, mul_assoc]
        _ = - (ι Q (gamma Q 3) * ι Q (gamma Q 0) * algebraMap R _ (Q (gamma Q 1))) + (ι Q (gamma Q 0) * ι Q (gamma Q 3)) * algebraMap R _ (Q (gamma Q 1)) := by rw [sq1]
        _ = - (algebraMap R _ (Q (gamma Q 1)) * (ι Q (gamma Q 3) * ι Q (gamma Q 0))) + algebraMap R _ (Q (gamma Q 1)) * (ι Q (gamma Q 0) * ι Q (gamma Q 3)) := by rw [Algebra.commutes, Algebra.commutes (Q (gamma Q 1))]
        _ = - (algebraMap R _ (Q (gamma Q 1)) * (ι Q (gamma Q 3) * ι Q (gamma Q 0))) + algebraMap R _ (Q (gamma Q 1)) * - (ι Q (gamma Q 3) * ι Q (gamma Q 0)) := by rw [h30]
        _ = - (algebraMap R _ (Q (gamma Q 1)) * (ι Q (gamma Q 3) * ι Q (gamma Q 0))) - algebraMap R _ (Q (gamma Q 1)) * (ι Q (gamma Q 3) * ι Q (gamma Q 0)) := by simp only [mul_neg, neg_mul, sub_eq_add_neg, ←mul_assoc, mul_assoc]
        _ = (- 2 : R) • (algebraMap R _ (Q (gamma Q 1)) * (ι Q (gamma Q 3) * ι Q (gamma Q 0))) := by simp only [neg_sub_neg, smul_eq_mul, neg_smul]; ring
    have H2 : ι Q (gamma Q 3) * ι Q (gamma Q 0) = - basisBivector Q 2 := by rw [←h30]; rfl
    rw [H, H2]; simp only [mul_neg]; exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨2, rfl⟩))
  · -- 4, 1
    dsimp [basisBivector]
    have H : (ι Q (gamma Q 3) * ι Q (gamma Q 1)) * (ι Q (gamma Q 0) * ι Q (gamma Q 2)) - (ι Q (gamma Q 0) * ι Q (gamma Q 2)) * (ι Q (gamma Q 3) * ι Q (gamma Q 1)) = 0 := by
      calc (ι Q (gamma Q 3) * ι Q (gamma Q 1)) * (ι Q (gamma Q 0) * ι Q (gamma Q 2)) - (ι Q (gamma Q 0) * ι Q (gamma Q 2)) * (ι Q (gamma Q 3) * ι Q (gamma Q 1))
        _ = ι Q (gamma Q 3) * ι Q (gamma Q 1) * ι Q (gamma Q 0) * ι Q (gamma Q 2) - ι Q (gamma Q 0) * ι Q (gamma Q 2) * ι Q (gamma Q 3) * ι Q (gamma Q 1) := by simp only [mul_assoc]
        _ = ι Q (gamma Q 3) * ι Q (gamma Q 1) * ι Q (gamma Q 0) * ι Q (gamma Q 2) - ι Q (gamma Q 0) * (ι Q (gamma Q 2) * ι Q (gamma Q 3)) * ι Q (gamma Q 1) := by simp only [←mul_assoc, mul_assoc]
        _ = ι Q (gamma Q 3) * ι Q (gamma Q 1) * ι Q (gamma Q 0) * ι Q (gamma Q 2) - ι Q (gamma Q 0) * - (ι Q (gamma Q 3) * ι Q (gamma Q 2)) * ι Q (gamma Q 1) := by rw [h32]
        _ = ι Q (gamma Q 3) * ι Q (gamma Q 1) * ι Q (gamma Q 0) * ι Q (gamma Q 2) + (ι Q (gamma Q 0) * ι Q (gamma Q 3)) * ι Q (gamma Q 2) * ι Q (gamma Q 1) := by simp only [mul_neg, neg_mul, sub_neg_eq_add, ←mul_assoc, mul_assoc]
        _ = ι Q (gamma Q 3) * ι Q (gamma Q 1) * ι Q (gamma Q 0) * ι Q (gamma Q 2) + - (ι Q (gamma Q 3) * ι Q (gamma Q 0)) * ι Q (gamma Q 2) * ι Q (gamma Q 1) := by rw [h30]
        _ = ι Q (gamma Q 3) * ι Q (gamma Q 1) * ι Q (gamma Q 0) * ι Q (gamma Q 2) - ι Q (gamma Q 3) * ι Q (gamma Q 0) * (ι Q (gamma Q 2) * ι Q (gamma Q 1)) := by simp only [neg_mul, mul_neg, ←mul_assoc, mul_assoc, sub_eq_add_neg, neg_neg]
        _ = ι Q (gamma Q 3) * ι Q (gamma Q 1) * ι Q (gamma Q 0) * ι Q (gamma Q 2) - ι Q (gamma Q 3) * ι Q (gamma Q 0) * - (ι Q (gamma Q 1) * ι Q (gamma Q 2)) := by rw [h21]
        _ = ι Q (gamma Q 3) * ι Q (gamma Q 1) * ι Q (gamma Q 0) * ι Q (gamma Q 2) + ι Q (gamma Q 3) * (ι Q (gamma Q 0) * ι Q (gamma Q 1)) * ι Q (gamma Q 2) := by simp only [mul_neg, neg_mul, sub_neg_eq_add, ←mul_assoc, mul_assoc]
        _ = ι Q (gamma Q 3) * ι Q (gamma Q 1) * ι Q (gamma Q 0) * ι Q (gamma Q 2) + ι Q (gamma Q 3) * - (ι Q (gamma Q 1) * ι Q (gamma Q 0)) * ι Q (gamma Q 2) := by rw [h10]
        _ = ι Q (gamma Q 3) * ι Q (gamma Q 1) * ι Q (gamma Q 0) * ι Q (gamma Q 2) - ι Q (gamma Q 3) * ι Q (gamma Q 1) * ι Q (gamma Q 0) * ι Q (gamma Q 2) := by simp only [mul_neg, neg_mul, sub_eq_add_neg, ←mul_assoc, mul_assoc]
        _ = 0 := by rw [sub_self]
    rw [H]; exact Submodule.zero_mem _
  · -- 4, 2
    dsimp [basisBivector]
    have H : (ι Q (gamma Q 3) * ι Q (gamma Q 1)) * (ι Q (gamma Q 0) * ι Q (gamma Q 3)) - (ι Q (gamma Q 0) * ι Q (gamma Q 3)) * (ι Q (gamma Q 3) * ι Q (gamma Q 1)) = (2 : R) • (algebraMap R _ (Q (gamma Q 3)) * (ι Q (gamma Q 1) * ι Q (gamma Q 0))) := by
      calc (ι Q (gamma Q 3) * ι Q (gamma Q 1)) * (ι Q (gamma Q 0) * ι Q (gamma Q 3)) - (ι Q (gamma Q 0) * ι Q (gamma Q 3)) * (ι Q (gamma Q 3) * ι Q (gamma Q 1))
        _ = ι Q (gamma Q 3) * (ι Q (gamma Q 1) * ι Q (gamma Q 0)) * ι Q (gamma Q 3) - ι Q (gamma Q 0) * (ι Q (gamma Q 3) * ι Q (gamma Q 3)) * ι Q (gamma Q 1) := by simp only [mul_assoc, ←mul_assoc]
        _ = ι Q (gamma Q 3) * (ι Q (gamma Q 1) * ι Q (gamma Q 0)) * ι Q (gamma Q 3) - ι Q (gamma Q 0) * algebraMap R _ (Q (gamma Q 3)) * ι Q (gamma Q 1) := by rw [sq3]
        _ = ι Q (gamma Q 3) * - (ι Q (gamma Q 0) * ι Q (gamma Q 1)) * ι Q (gamma Q 3) - algebraMap R _ (Q (gamma Q 3)) * (ι Q (gamma Q 0) * ι Q (gamma Q 1)) := by rw [h10, Algebra.commutes]
        _ = - (ι Q (gamma Q 3) * ι Q (gamma Q 0) * ι Q (gamma Q 1) * ι Q (gamma Q 3)) - algebraMap R _ (Q (gamma Q 3)) * (ι Q (gamma Q 0) * ι Q (gamma Q 1)) := by simp only [mul_neg, neg_mul, ←mul_assoc, mul_assoc]
        _ = - (ι Q (gamma Q 3) * ι Q (gamma Q 0) * (ι Q (gamma Q 1) * ι Q (gamma Q 3))) - algebraMap R _ (Q (gamma Q 3)) * (ι Q (gamma Q 0) * ι Q (gamma Q 1)) := by simp only [mul_assoc]
        _ = - (ι Q (gamma Q 3) * ι Q (gamma Q 0) * - (ι Q (gamma Q 3) * ι Q (gamma Q 1))) - algebraMap R _ (Q (gamma Q 3)) * (ι Q (gamma Q 0) * ι Q (gamma Q 1)) := by rw [h31]
        _ = ι Q (gamma Q 3) * (ι Q (gamma Q 0) * ι Q (gamma Q 3)) * ι Q (gamma Q 1) - algebraMap R _ (Q (gamma Q 3)) * (ι Q (gamma Q 0) * ι Q (gamma Q 1)) := by simp only [mul_neg, neg_mul, neg_neg, ←mul_assoc, mul_assoc]
        _ = ι Q (gamma Q 3) * - (ι Q (gamma Q 3) * ι Q (gamma Q 0)) * ι Q (gamma Q 1) - algebraMap R _ (Q (gamma Q 3)) * (ι Q (gamma Q 0) * ι Q (gamma Q 1)) := by rw [h30]
        _ = - ((ι Q (gamma Q 3) * ι Q (gamma Q 3)) * (ι Q (gamma Q 0) * ι Q (gamma Q 1))) - algebraMap R _ (Q (gamma Q 3)) * (ι Q (gamma Q 0) * ι Q (gamma Q 1)) := by simp only [mul_neg, neg_mul, ←mul_assoc, mul_assoc]
        _ = - (algebraMap R _ (Q (gamma Q 3)) * (ι Q (gamma Q 0) * ι Q (gamma Q 1))) - algebraMap R _ (Q (gamma Q 3)) * (ι Q (gamma Q 0) * ι Q (gamma Q 1)) := by rw [sq3]
        _ = - (algebraMap R _ (Q (gamma Q 3)) * - (ι Q (gamma Q 1) * ι Q (gamma Q 0))) - algebraMap R _ (Q (gamma Q 3)) * - (ι Q (gamma Q 1) * ι Q (gamma Q 0)) := by rw [h10]
        _ = algebraMap R _ (Q (gamma Q 3)) * (ι Q (gamma Q 1) * ι Q (gamma Q 0)) + algebraMap R _ (Q (gamma Q 3)) * (ι Q (gamma Q 1) * ι Q (gamma Q 0)) := by simp only [mul_neg, neg_mul, sub_eq_add_neg, neg_neg]
        _ = (2 : R) • (algebraMap R _ (Q (gamma Q 3)) * (ι Q (gamma Q 1) * ι Q (gamma Q 0))) := by simp only [smul_eq_mul]; ring
    have H2 : ι Q (gamma Q 1) * ι Q (gamma Q 0) = - basisBivector Q 0 := by rw [←h10]; rfl
    rw [H, H2]; simp only [mul_neg]; exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩))
  · -- 4, 3
    dsimp [basisBivector]
    have H : (ι Q (gamma Q 3) * ι Q (gamma Q 1)) * (ι Q (gamma Q 2) * ι Q (gamma Q 3)) - (ι Q (gamma Q 2) * ι Q (gamma Q 3)) * (ι Q (gamma Q 3) * ι Q (gamma Q 1)) = (2 : R) • (algebraMap R _ (Q (gamma Q 3)) * (ι Q (gamma Q 1) * ι Q (gamma Q 2))) := by
      calc (ι Q (gamma Q 3) * ι Q (gamma Q 1)) * (ι Q (gamma Q 2) * ι Q (gamma Q 3)) - (ι Q (gamma Q 2) * ι Q (gamma Q 3)) * (ι Q (gamma Q 3) * ι Q (gamma Q 1))
        _ = ι Q (gamma Q 3) * (ι Q (gamma Q 1) * ι Q (gamma Q 2)) * ι Q (gamma Q 3) - ι Q (gamma Q 2) * (ι Q (gamma Q 3) * ι Q (gamma Q 3)) * ι Q (gamma Q 1) := by simp only [mul_assoc, ←mul_assoc]
        _ = ι Q (gamma Q 3) * (ι Q (gamma Q 1) * ι Q (gamma Q 2)) * ι Q (gamma Q 3) - ι Q (gamma Q 2) * algebraMap R _ (Q (gamma Q 3)) * ι Q (gamma Q 1) := by rw [sq3]
        _ = ι Q (gamma Q 3) * - (ι Q (gamma Q 2) * ι Q (gamma Q 1)) * ι Q (gamma Q 3) - algebraMap R _ (Q (gamma Q 3)) * (ι Q (gamma Q 2) * ι Q (gamma Q 1)) := by rw [h21, Algebra.commutes]
        _ = - (ι Q (gamma Q 3) * ι Q (gamma Q 2) * ι Q (gamma Q 1) * ι Q (gamma Q 3)) - algebraMap R _ (Q (gamma Q 3)) * (ι Q (gamma Q 2) * ι Q (gamma Q 1)) := by simp only [mul_neg, neg_mul, ←mul_assoc, mul_assoc]
        _ = - (ι Q (gamma Q 3) * ι Q (gamma Q 2) * (ι Q (gamma Q 1) * ι Q (gamma Q 3))) - algebraMap R _ (Q (gamma Q 3)) * (ι Q (gamma Q 2) * ι Q (gamma Q 1)) := by simp only [mul_assoc]
        _ = - (ι Q (gamma Q 3) * ι Q (gamma Q 2) * - (ι Q (gamma Q 3) * ι Q (gamma Q 1))) - algebraMap R _ (Q (gamma Q 3)) * (ι Q (gamma Q 2) * ι Q (gamma Q 1)) := by rw [h31]
        _ = ι Q (gamma Q 3) * (ι Q (gamma Q 2) * ι Q (gamma Q 3)) * ι Q (gamma Q 1) - algebraMap R _ (Q (gamma Q 3)) * (ι Q (gamma Q 2) * ι Q (gamma Q 1)) := by simp only [mul_neg, neg_mul, neg_neg, ←mul_assoc, mul_assoc]
        _ = ι Q (gamma Q 3) * - (ι Q (gamma Q 3) * ι Q (gamma Q 2)) * ι Q (gamma Q 1) - algebraMap R _ (Q (gamma Q 3)) * (ι Q (gamma Q 2) * ι Q (gamma Q 1)) := by rw [h32]
        _ = - ((ι Q (gamma Q 3) * ι Q (gamma Q 3)) * (ι Q (gamma Q 2) * ι Q (gamma Q 1))) - algebraMap R _ (Q (gamma Q 3)) * (ι Q (gamma Q 2) * ι Q (gamma Q 1)) := by simp only [mul_neg, neg_mul, ←mul_assoc, mul_assoc]
        _ = - (algebraMap R _ (Q (gamma Q 3)) * (ι Q (gamma Q 2) * ι Q (gamma Q 1))) - algebraMap R _ (Q (gamma Q 3)) * (ι Q (gamma Q 2) * ι Q (gamma Q 1)) := by rw [sq3]
        _ = - (algebraMap R _ (Q (gamma Q 3)) * - (ι Q (gamma Q 1) * ι Q (gamma Q 2))) - algebraMap R _ (Q (gamma Q 3)) * - (ι Q (gamma Q 1) * ι Q (gamma Q 2)) := by rw [h21]
        _ = algebraMap R _ (Q (gamma Q 3)) * (ι Q (gamma Q 1) * ι Q (gamma Q 2)) + algebraMap R _ (Q (gamma Q 3)) * (ι Q (gamma Q 1) * ι Q (gamma Q 2)) := by simp only [mul_neg, neg_mul, sub_eq_add_neg, neg_neg]
        _ = (2 : R) • (algebraMap R _ (Q (gamma Q 3)) * (ι Q (gamma Q 1) * ι Q (gamma Q 2))) := by simp only [smul_eq_mul]; ring
    have H2 : ι Q (gamma Q 1) * ι Q (gamma Q 2) = basisBivector Q 5 := rfl
    rw [H, H2]; exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨5, rfl⟩))
  · -- 4, 4
    dsimp [basisBivector]
    have H : ι Q (gamma Q 3) * ι Q (gamma Q 1) * (ι Q (gamma Q 3) * ι Q (gamma Q 1)) - ι Q (gamma Q 3) * ι Q (gamma Q 1) * (ι Q (gamma Q 3) * ι Q (gamma Q 1)) = 0 := by rw [sub_self]
    rw [H]; exact Submodule.zero_mem _
  · -- 4, 5
    dsimp [basisBivector]
    have H : (ι Q (gamma Q 3) * ι Q (gamma Q 1)) * (ι Q (gamma Q 1) * ι Q (gamma Q 2)) - (ι Q (gamma Q 1) * ι Q (gamma Q 2)) * (ι Q (gamma Q 3) * ι Q (gamma Q 1)) = (2 : R) • (algebraMap R _ (Q (gamma Q 1)) * (ι Q (gamma Q 3) * ι Q (gamma Q 2))) := by
      calc (ι Q (gamma Q 3) * ι Q (gamma Q 1)) * (ι Q (gamma Q 1) * ι Q (gamma Q 2)) - (ι Q (gamma Q 1) * ι Q (gamma Q 2)) * (ι Q (gamma Q 3) * ι Q (gamma Q 1))
        _ = ι Q (gamma Q 3) * (ι Q (gamma Q 1) * ι Q (gamma Q 1)) * ι Q (gamma Q 2) - ι Q (gamma Q 1) * (ι Q (gamma Q 2) * ι Q (gamma Q 3)) * ι Q (gamma Q 1) := by simp only [mul_assoc, ←mul_assoc]
        _ = ι Q (gamma Q 3) * algebraMap R _ (Q (gamma Q 1)) * ι Q (gamma Q 2) - ι Q (gamma Q 1) * (ι Q (gamma Q 2) * ι Q (gamma Q 3)) * ι Q (gamma Q 1) := by rw [sq1]
        _ = algebraMap R _ (Q (gamma Q 1)) * (ι Q (gamma Q 3) * ι Q (gamma Q 2)) - ι Q (gamma Q 1) * - (ι Q (gamma Q 3) * ι Q (gamma Q 2)) * ι Q (gamma Q 1) := by rw [h32, Algebra.commutes]
        _ = algebraMap R _ (Q (gamma Q 1)) * (ι Q (gamma Q 3) * ι Q (gamma Q 2)) + (ι Q (gamma Q 1) * ι Q (gamma Q 3)) * ι Q (gamma Q 2) * ι Q (gamma Q 1) := by simp only [mul_neg, neg_mul, sub_neg_eq_add, ←mul_assoc, mul_assoc]
        _ = algebraMap R _ (Q (gamma Q 1)) * (ι Q (gamma Q 3) * ι Q (gamma Q 2)) + - (ι Q (gamma Q 3) * ι Q (gamma Q 1)) * ι Q (gamma Q 2) * ι Q (gamma Q 1) := by rw [h31]
        _ = algebraMap R _ (Q (gamma Q 1)) * (ι Q (gamma Q 3) * ι Q (gamma Q 2)) - ι Q (gamma Q 3) * (ι Q (gamma Q 1) * ι Q (gamma Q 2)) * ι Q (gamma Q 1) := by simp only [mul_neg, neg_mul, ←mul_assoc, mul_assoc, sub_eq_add_neg, neg_neg]
        _ = algebraMap R _ (Q (gamma Q 1)) * (ι Q (gamma Q 3) * ι Q (gamma Q 2)) - ι Q (gamma Q 3) * - (ι Q (gamma Q 2) * ι Q (gamma Q 1)) * ι Q (gamma Q 1) := by rw [h21]
        _ = algebraMap R _ (Q (gamma Q 1)) * (ι Q (gamma Q 3) * ι Q (gamma Q 2)) + ι Q (gamma Q 3) * ι Q (gamma Q 2) * (ι Q (gamma Q 1) * ι Q (gamma Q 1)) := by simp only [mul_neg, neg_mul, sub_neg_eq_add, ←mul_assoc, mul_assoc]
        _ = algebraMap R _ (Q (gamma Q 1)) * (ι Q (gamma Q 3) * ι Q (gamma Q 2)) + ι Q (gamma Q 3) * ι Q (gamma Q 2) * algebraMap R _ (Q (gamma Q 1)) := by rw [sq1]
        _ = algebraMap R _ (Q (gamma Q 1)) * (ι Q (gamma Q 3) * ι Q (gamma Q 2)) + algebraMap R _ (Q (gamma Q 1)) * (ι Q (gamma Q 3) * ι Q (gamma Q 2)) := by rw [Algebra.commutes (Q (gamma Q 1))]
        _ = (2 : R) • (algebraMap R _ (Q (gamma Q 1)) * (ι Q (gamma Q 3) * ι Q (gamma Q 2))) := by simp only [smul_eq_mul]; ring
    have H2 : ι Q (gamma Q 3) * ι Q (gamma Q 2) = - basisBivector Q 3 := by rw [←h32]; rfl
    rw [H, H2]; simp only [mul_neg]; exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨3, rfl⟩))
  · -- 5, 0
    dsimp [basisBivector]
    have H : (ι Q (gamma Q 1) * ι Q (gamma Q 2)) * (ι Q (gamma Q 0) * ι Q (gamma Q 1)) - (ι Q (gamma Q 0) * ι Q (gamma Q 1)) * (ι Q (gamma Q 1) * ι Q (gamma Q 2)) = (2 : R) • (algebraMap R _ (Q (gamma Q 1)) * (ι Q (gamma Q 2) * ι Q (gamma Q 0))) := by
      calc (ι Q (gamma Q 1) * ι Q (gamma Q 2)) * (ι Q (gamma Q 0) * ι Q (gamma Q 1)) - (ι Q (gamma Q 0) * ι Q (gamma Q 1)) * (ι Q (gamma Q 1) * ι Q (gamma Q 2))
        _ = ι Q (gamma Q 1) * (ι Q (gamma Q 2) * ι Q (gamma Q 0)) * ι Q (gamma Q 1) - ι Q (gamma Q 0) * (ι Q (gamma Q 1) * ι Q (gamma Q 1)) * ι Q (gamma Q 2) := by simp only [mul_assoc, ←mul_assoc]
        _ = ι Q (gamma Q 1) * (ι Q (gamma Q 2) * ι Q (gamma Q 0)) * ι Q (gamma Q 1) - ι Q (gamma Q 0) * algebraMap R _ (Q (gamma Q 1)) * ι Q (gamma Q 2) := by rw [sq1]
        _ = ι Q (gamma Q 1) * - (ι Q (gamma Q 0) * ι Q (gamma Q 2)) * ι Q (gamma Q 1) - algebraMap R _ (Q (gamma Q 1)) * (ι Q (gamma Q 0) * ι Q (gamma Q 2)) := by rw [h20, Algebra.commutes]
        _ = - (ι Q (gamma Q 1) * ι Q (gamma Q 0) * ι Q (gamma Q 2) * ι Q (gamma Q 1)) - algebraMap R _ (Q (gamma Q 1)) * (ι Q (gamma Q 0) * ι Q (gamma Q 2)) := by simp only [mul_neg, neg_mul, ←mul_assoc, mul_assoc]
        _ = - (ι Q (gamma Q 1) * ι Q (gamma Q 0) * (ι Q (gamma Q 2) * ι Q (gamma Q 1))) - algebraMap R _ (Q (gamma Q 1)) * (ι Q (gamma Q 0) * ι Q (gamma Q 2)) := by simp only [mul_assoc]
        _ = - (ι Q (gamma Q 1) * ι Q (gamma Q 0) * - (ι Q (gamma Q 1) * ι Q (gamma Q 2))) - algebraMap R _ (Q (gamma Q 1)) * (ι Q (gamma Q 0) * ι Q (gamma Q 2)) := by rw [h21]
        _ = ι Q (gamma Q 1) * (ι Q (gamma Q 0) * ι Q (gamma Q 1)) * ι Q (gamma Q 2) - algebraMap R _ (Q (gamma Q 1)) * (ι Q (gamma Q 0) * ι Q (gamma Q 2)) := by simp only [mul_neg, neg_mul, neg_neg, ←mul_assoc, mul_assoc]
        _ = ι Q (gamma Q 1) * - (ι Q (gamma Q 1) * ι Q (gamma Q 0)) * ι Q (gamma Q 2) - algebraMap R _ (Q (gamma Q 1)) * (ι Q (gamma Q 0) * ι Q (gamma Q 2)) := by rw [h10]
        _ = - ((ι Q (gamma Q 1) * ι Q (gamma Q 1)) * (ι Q (gamma Q 0) * ι Q (gamma Q 2))) - algebraMap R _ (Q (gamma Q 1)) * (ι Q (gamma Q 0) * ι Q (gamma Q 2)) := by simp only [mul_neg, neg_mul, ←mul_assoc, mul_assoc]
        _ = - (algebraMap R _ (Q (gamma Q 1)) * (ι Q (gamma Q 0) * ι Q (gamma Q 2))) - algebraMap R _ (Q (gamma Q 1)) * (ι Q (gamma Q 0) * ι Q (gamma Q 2)) := by rw [sq1]
        _ = - (algebraMap R _ (Q (gamma Q 1)) * - (ι Q (gamma Q 2) * ι Q (gamma Q 0))) - algebraMap R _ (Q (gamma Q 1)) * - (ι Q (gamma Q 2) * ι Q (gamma Q 0)) := by rw [h20]
        _ = algebraMap R _ (Q (gamma Q 1)) * (ι Q (gamma Q 2) * ι Q (gamma Q 0)) + algebraMap R _ (Q (gamma Q 1)) * (ι Q (gamma Q 2) * ι Q (gamma Q 0)) := by simp only [mul_neg, neg_mul, sub_eq_add_neg, neg_neg]
        _ = (2 : R) • (algebraMap R _ (Q (gamma Q 1)) * (ι Q (gamma Q 2) * ι Q (gamma Q 0))) := by simp only [smul_eq_mul]; ring
    have H2 : ι Q (gamma Q 2) * ι Q (gamma Q 0) = - basisBivector Q 1 := by rw [←h20]; rfl
    rw [H, H2]; simp only [mul_neg]; exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, rfl⟩))
  · -- 5, 1
    dsimp [basisBivector]
    have H : (ι Q (gamma Q 1) * ι Q (gamma Q 2)) * (ι Q (gamma Q 0) * ι Q (gamma Q 2)) - (ι Q (gamma Q 0) * ι Q (gamma Q 2)) * (ι Q (gamma Q 1) * ι Q (gamma Q 2)) = (- 2 : R) • (algebraMap R _ (Q (gamma Q 2)) * (ι Q (gamma Q 1) * ι Q (gamma Q 0))) := by
      calc (ι Q (gamma Q 1) * ι Q (gamma Q 2)) * (ι Q (gamma Q 0) * ι Q (gamma Q 2)) - (ι Q (gamma Q 0) * ι Q (gamma Q 2)) * (ι Q (gamma Q 1) * ι Q (gamma Q 2))
        _ = ι Q (gamma Q 1) * (ι Q (gamma Q 2) * ι Q (gamma Q 0)) * ι Q (gamma Q 2) - ι Q (gamma Q 0) * (ι Q (gamma Q 2) * ι Q (gamma Q 1)) * ι Q (gamma Q 2) := by simp only [mul_assoc, ←mul_assoc]
        _ = ι Q (gamma Q 1) * - (ι Q (gamma Q 0) * ι Q (gamma Q 2)) * ι Q (gamma Q 2) - ι Q (gamma Q 0) * - (ι Q (gamma Q 1) * ι Q (gamma Q 2)) * ι Q (gamma Q 2) := by rw [h20, h21]
        _ = - (ι Q (gamma Q 1) * ι Q (gamma Q 0) * (ι Q (gamma Q 2) * ι Q (gamma Q 2))) + ι Q (gamma Q 0) * ι Q (gamma Q 1) * (ι Q (gamma Q 2) * ι Q (gamma Q 2)) := by simp only [mul_neg, neg_mul, sub_neg_eq_add, ←mul_assoc, mul_assoc]
        _ = - (ι Q (gamma Q 1) * ι Q (gamma Q 0) * algebraMap R _ (Q (gamma Q 2))) + (ι Q (gamma Q 0) * ι Q (gamma Q 1)) * algebraMap R _ (Q (gamma Q 2)) := by rw [sq2]
        _ = - (algebraMap R _ (Q (gamma Q 2)) * (ι Q (gamma Q 1) * ι Q (gamma Q 0))) + algebraMap R _ (Q (gamma Q 2)) * (ι Q (gamma Q 0) * ι Q (gamma Q 1)) := by rw [Algebra.commutes, Algebra.commutes (Q (gamma Q 2))]
        _ = - (algebraMap R _ (Q (gamma Q 2)) * (ι Q (gamma Q 1) * ι Q (gamma Q 0))) + algebraMap R _ (Q (gamma Q 2)) * - (ι Q (gamma Q 1) * ι Q (gamma Q 0)) := by rw [h10]
        _ = - (algebraMap R _ (Q (gamma Q 2)) * (ι Q (gamma Q 1) * ι Q (gamma Q 0))) - algebraMap R _ (Q (gamma Q 2)) * (ι Q (gamma Q 1) * ι Q (gamma Q 0)) := by simp only [mul_neg, neg_mul, sub_eq_add_neg, ←mul_assoc, mul_assoc]
        _ = (- 2 : R) • (algebraMap R _ (Q (gamma Q 2)) * (ι Q (gamma Q 1) * ι Q (gamma Q 0))) := by simp only [neg_sub_neg, smul_eq_mul, neg_smul]; ring
    have H2 : ι Q (gamma Q 1) * ι Q (gamma Q 0) = - basisBivector Q 0 := by rw [←h10]; rfl
    rw [H, H2]; simp only [mul_neg]; exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩))
  · -- 5, 2
    dsimp [basisBivector]
    have H : (ι Q (gamma Q 1) * ι Q (gamma Q 2)) * (ι Q (gamma Q 0) * ι Q (gamma Q 3)) - (ι Q (gamma Q 0) * ι Q (gamma Q 3)) * (ι Q (gamma Q 1) * ι Q (gamma Q 2)) = 0 := by
      calc (ι Q (gamma Q 1) * ι Q (gamma Q 2)) * (ι Q (gamma Q 0) * ι Q (gamma Q 3)) - (ι Q (gamma Q 0) * ι Q (gamma Q 3)) * (ι Q (gamma Q 1) * ι Q (gamma Q 2))
        _ = ι Q (gamma Q 1) * ι Q (gamma Q 2) * ι Q (gamma Q 0) * ι Q (gamma Q 3) - ι Q (gamma Q 0) * ι Q (gamma Q 3) * ι Q (gamma Q 1) * ι Q (gamma Q 2) := by simp only [mul_assoc]
        _ = ι Q (gamma Q 1) * ι Q (gamma Q 2) * ι Q (gamma Q 0) * ι Q (gamma Q 3) - ι Q (gamma Q 0) * (ι Q (gamma Q 3) * ι Q (gamma Q 1)) * ι Q (gamma Q 2) := by simp only [←mul_assoc, mul_assoc]
        _ = ι Q (gamma Q 1) * ι Q (gamma Q 2) * ι Q (gamma Q 0) * ι Q (gamma Q 3) - ι Q (gamma Q 0) * - (ι Q (gamma Q 1) * ι Q (gamma Q 3)) * ι Q (gamma Q 2) := by rw [h31]
        _ = ι Q (gamma Q 1) * ι Q (gamma Q 2) * ι Q (gamma Q 0) * ι Q (gamma Q 3) + (ι Q (gamma Q 0) * ι Q (gamma Q 1)) * ι Q (gamma Q 3) * ι Q (gamma Q 2) := by simp only [mul_neg, neg_mul, sub_neg_eq_add, ←mul_assoc, mul_assoc]
        _ = ι Q (gamma Q 1) * ι Q (gamma Q 2) * ι Q (gamma Q 0) * ι Q (gamma Q 3) + - (ι Q (gamma Q 1) * ι Q (gamma Q 0)) * ι Q (gamma Q 3) * ι Q (gamma Q 2) := by rw [h10]
        _ = ι Q (gamma Q 1) * ι Q (gamma Q 2) * ι Q (gamma Q 0) * ι Q (gamma Q 3) - ι Q (gamma Q 1) * ι Q (gamma Q 0) * (ι Q (gamma Q 3) * ι Q (gamma Q 2)) := by simp only [neg_mul, mul_neg, ←mul_assoc, mul_assoc, sub_eq_add_neg, neg_neg]
        _ = ι Q (gamma Q 1) * ι Q (gamma Q 2) * ι Q (gamma Q 0) * ι Q (gamma Q 3) - ι Q (gamma Q 1) * ι Q (gamma Q 0) * - (ι Q (gamma Q 2) * ι Q (gamma Q 3)) := by rw [h32]
        _ = ι Q (gamma Q 1) * ι Q (gamma Q 2) * ι Q (gamma Q 0) * ι Q (gamma Q 3) + ι Q (gamma Q 1) * (ι Q (gamma Q 0) * ι Q (gamma Q 2)) * ι Q (gamma Q 3) := by simp only [mul_neg, neg_mul, sub_neg_eq_add, ←mul_assoc, mul_assoc]
        _ = ι Q (gamma Q 1) * ι Q (gamma Q 2) * ι Q (gamma Q 0) * ι Q (gamma Q 3) + ι Q (gamma Q 1) * - (ι Q (gamma Q 2) * ι Q (gamma Q 0)) * ι Q (gamma Q 3) := by rw [h20]
        _ = ι Q (gamma Q 1) * ι Q (gamma Q 2) * ι Q (gamma Q 0) * ι Q (gamma Q 3) - ι Q (gamma Q 1) * ι Q (gamma Q 2) * ι Q (gamma Q 0) * ι Q (gamma Q 3) := by simp only [mul_neg, neg_mul, sub_eq_add_neg, ←mul_assoc, mul_assoc]
        _ = 0 := by rw [sub_self]
    rw [H]; exact Submodule.zero_mem _
  · -- 5, 3
    dsimp [basisBivector]
    have H : (ι Q (gamma Q 1) * ι Q (gamma Q 2)) * (ι Q (gamma Q 2) * ι Q (gamma Q 3)) - (ι Q (gamma Q 2) * ι Q (gamma Q 3)) * (ι Q (gamma Q 1) * ι Q (gamma Q 2)) = (2 : R) • (algebraMap R _ (Q (gamma Q 2)) * (ι Q (gamma Q 1) * ι Q (gamma Q 3))) := by
      calc (ι Q (gamma Q 1) * ι Q (gamma Q 2)) * (ι Q (gamma Q 2) * ι Q (gamma Q 3)) - (ι Q (gamma Q 2) * ι Q (gamma Q 3)) * (ι Q (gamma Q 1) * ι Q (gamma Q 2))
        _ = ι Q (gamma Q 1) * (ι Q (gamma Q 2) * ι Q (gamma Q 2)) * ι Q (gamma Q 3) - ι Q (gamma Q 2) * (ι Q (gamma Q 3) * ι Q (gamma Q 1)) * ι Q (gamma Q 2) := by simp only [mul_assoc, ←mul_assoc]
        _ = ι Q (gamma Q 1) * algebraMap R _ (Q (gamma Q 2)) * ι Q (gamma Q 3) - ι Q (gamma Q 2) * (ι Q (gamma Q 3) * ι Q (gamma Q 1)) * ι Q (gamma Q 2) := by rw [sq2]
        _ = algebraMap R _ (Q (gamma Q 2)) * (ι Q (gamma Q 1) * ι Q (gamma Q 3)) - ι Q (gamma Q 2) * - (ι Q (gamma Q 1) * ι Q (gamma Q 3)) * ι Q (gamma Q 2) := by rw [h31, Algebra.commutes]
        _ = algebraMap R _ (Q (gamma Q 2)) * (ι Q (gamma Q 1) * ι Q (gamma Q 3)) + (ι Q (gamma Q 2) * ι Q (gamma Q 1)) * ι Q (gamma Q 3) * ι Q (gamma Q 2) := by simp only [mul_neg, neg_mul, sub_neg_eq_add, ←mul_assoc, mul_assoc]
        _ = algebraMap R _ (Q (gamma Q 2)) * (ι Q (gamma Q 1) * ι Q (gamma Q 3)) + - (ι Q (gamma Q 1) * ι Q (gamma Q 2)) * ι Q (gamma Q 3) * ι Q (gamma Q 2) := by rw [h21]
        _ = algebraMap R _ (Q (gamma Q 2)) * (ι Q (gamma Q 1) * ι Q (gamma Q 3)) - ι Q (gamma Q 1) * (ι Q (gamma Q 2) * ι Q (gamma Q 3)) * ι Q (gamma Q 2) := by simp only [mul_neg, neg_mul, ←mul_assoc, mul_assoc, sub_eq_add_neg, neg_neg]
        _ = algebraMap R _ (Q (gamma Q 2)) * (ι Q (gamma Q 1) * ι Q (gamma Q 3)) - ι Q (gamma Q 1) * - (ι Q (gamma Q 3) * ι Q (gamma Q 2)) * ι Q (gamma Q 2) := by rw [h32]
        _ = algebraMap R _ (Q (gamma Q 2)) * (ι Q (gamma Q 1) * ι Q (gamma Q 3)) + ι Q (gamma Q 1) * ι Q (gamma Q 3) * (ι Q (gamma Q 2) * ι Q (gamma Q 2)) := by simp only [mul_neg, neg_mul, sub_neg_eq_add, ←mul_assoc, mul_assoc]
        _ = algebraMap R _ (Q (gamma Q 2)) * (ι Q (gamma Q 1) * ι Q (gamma Q 3)) + ι Q (gamma Q 1) * ι Q (gamma Q 3) * algebraMap R _ (Q (gamma Q 2)) := by rw [sq2]
        _ = algebraMap R _ (Q (gamma Q 2)) * (ι Q (gamma Q 1) * ι Q (gamma Q 3)) + algebraMap R _ (Q (gamma Q 2)) * (ι Q (gamma Q 1) * ι Q (gamma Q 3)) := by rw [Algebra.commutes (Q (gamma Q 2))]
        _ = (2 : R) • (algebraMap R _ (Q (gamma Q 2)) * (ι Q (gamma Q 1) * ι Q (gamma Q 3))) := by simp only [smul_eq_mul]; ring
    have H2 : ι Q (gamma Q 1) * ι Q (gamma Q 3) = - basisBivector Q 4 := by rw [←h31]; rfl
    rw [H, H2]; simp only [mul_neg]; exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨4, rfl⟩))
  · -- 5, 4
    dsimp [basisBivector]
    have H : (ι Q (gamma Q 1) * ι Q (gamma Q 2)) * (ι Q (gamma Q 3) * ι Q (gamma Q 1)) - (ι Q (gamma Q 3) * ι Q (gamma Q 1)) * (ι Q (gamma Q 1) * ι Q (gamma Q 2)) = (2 : R) • (algebraMap R _ (Q (gamma Q 1)) * (ι Q (gamma Q 2) * ι Q (gamma Q 3))) := by
      calc (ι Q (gamma Q 1) * ι Q (gamma Q 2)) * (ι Q (gamma Q 3) * ι Q (gamma Q 1)) - (ι Q (gamma Q 3) * ι Q (gamma Q 1)) * (ι Q (gamma Q 1) * ι Q (gamma Q 2))
        _ = ι Q (gamma Q 1) * (ι Q (gamma Q 2) * ι Q (gamma Q 3)) * ι Q (gamma Q 1) - ι Q (gamma Q 3) * (ι Q (gamma Q 1) * ι Q (gamma Q 1)) * ι Q (gamma Q 2) := by simp only [mul_assoc, ←mul_assoc]
        _ = ι Q (gamma Q 1) * (ι Q (gamma Q 2) * ι Q (gamma Q 3)) * ι Q (gamma Q 1) - ι Q (gamma Q 3) * algebraMap R _ (Q (gamma Q 1)) * ι Q (gamma Q 2) := by rw [sq1]
        _ = ι Q (gamma Q 1) * - (ι Q (gamma Q 3) * ι Q (gamma Q 2)) * ι Q (gamma Q 1) - algebraMap R _ (Q (gamma Q 1)) * (ι Q (gamma Q 3) * ι Q (gamma Q 2)) := by rw [h32, Algebra.commutes]
        _ = - (ι Q (gamma Q 1) * ι Q (gamma Q 3) * ι Q (gamma Q 2) * ι Q (gamma Q 1)) - algebraMap R _ (Q (gamma Q 1)) * (ι Q (gamma Q 3) * ι Q (gamma Q 2)) := by simp only [mul_neg, neg_mul, ←mul_assoc, mul_assoc]
        _ = - (ι Q (gamma Q 1) * ι Q (gamma Q 3) * (ι Q (gamma Q 2) * ι Q (gamma Q 1))) - algebraMap R _ (Q (gamma Q 1)) * (ι Q (gamma Q 3) * ι Q (gamma Q 2)) := by simp only [mul_assoc]
        _ = - (ι Q (gamma Q 1) * ι Q (gamma Q 3) * - (ι Q (gamma Q 1) * ι Q (gamma Q 2))) - algebraMap R _ (Q (gamma Q 1)) * (ι Q (gamma Q 3) * ι Q (gamma Q 2)) := by rw [h21]
        _ = ι Q (gamma Q 1) * (ι Q (gamma Q 3) * ι Q (gamma Q 1)) * ι Q (gamma Q 2) - algebraMap R _ (Q (gamma Q 1)) * (ι Q (gamma Q 3) * ι Q (gamma Q 2)) := by simp only [mul_neg, neg_mul, neg_neg, ←mul_assoc, mul_assoc]
        _ = ι Q (gamma Q 1) * - (ι Q (gamma Q 1) * ι Q (gamma Q 3)) * ι Q (gamma Q 2) - algebraMap R _ (Q (gamma Q 1)) * (ι Q (gamma Q 3) * ι Q (gamma Q 2)) := by rw [h31]
        _ = - ((ι Q (gamma Q 1) * ι Q (gamma Q 1)) * (ι Q (gamma Q 3) * ι Q (gamma Q 2))) - algebraMap R _ (Q (gamma Q 1)) * (ι Q (gamma Q 3) * ι Q (gamma Q 2)) := by simp only [mul_neg, neg_mul, ←mul_assoc, mul_assoc]
        _ = - (algebraMap R _ (Q (gamma Q 1)) * (ι Q (gamma Q 3) * ι Q (gamma Q 2))) - algebraMap R _ (Q (gamma Q 1)) * (ι Q (gamma Q 3) * ι Q (gamma Q 2)) := by rw [sq1]
        _ = - (algebraMap R _ (Q (gamma Q 1)) * - (ι Q (gamma Q 2) * ι Q (gamma Q 3))) - algebraMap R _ (Q (gamma Q 1)) * - (ι Q (gamma Q 2) * ι Q (gamma Q 3)) := by rw [h32]
        _ = algebraMap R _ (Q (gamma Q 1)) * (ι Q (gamma Q 2) * ι Q (gamma Q 3)) + algebraMap R _ (Q (gamma Q 1)) * (ι Q (gamma Q 2) * ι Q (gamma Q 3)) := by simp only [mul_neg, neg_mul, sub_eq_add_neg, neg_neg]
        _ = (2 : R) • (algebraMap R _ (Q (gamma Q 1)) * (ι Q (gamma Q 2) * ι Q (gamma Q 3))) := by simp only [smul_eq_mul]; ring
    have H2 : ι Q (gamma Q 2) * ι Q (gamma Q 3) = basisBivector Q 3 := rfl
    rw [H, H2]; exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨3, rfl⟩))
  · -- 5, 5
    dsimp [basisBivector]
    have H : ι Q (gamma Q 1) * ι Q (gamma Q 2) * (ι Q (gamma Q 1) * ι Q (gamma Q 2)) - ι Q (gamma Q 1) * ι Q (gamma Q 2) * (ι Q (gamma Q 1) * ι Q (gamma Q 2)) = 0 := by rw [sub_self]
    rw [H]; exact Submodule.zero_mem _

theorem bivector_commutator_mem (x y : CliffordAlgebra Q) (hx : x ∈ Bivector13 Q) (hy : y ∈ Bivector13 Q) :
    x * y - y * x ∈ Bivector13 Q := by
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
  · intro a ha
    rcases ha with ⟨i, hi⟩
    rw [← hi]
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hy
    · intro b hb
      rcases hb with ⟨j, hj⟩
      rw [← hj]
      exact basisBivector_commutator_mem Q i j
    · simp only [mul_zero, zero_mul, sub_zero, Submodule.zero_mem]
    · intro u v _ _ hu hv
      have H : basisBivector Q i * (u + v) - (u + v) * basisBivector Q i = (basisBivector Q i * u - u * basisBivector Q i) + (basisBivector Q i * v - v * basisBivector Q i) := by
        calc basisBivector Q i * (u + v) - (u + v) * basisBivector Q i
          _ = basisBivector Q i * u + basisBivector Q i * v - (u * basisBivector Q i + v * basisBivector Q i) := by rw [mul_add, add_mul]
          _ = (basisBivector Q i * u - u * basisBivector Q i) + (basisBivector Q i * v - v * basisBivector Q i) := by abel
      rw [H]
      exact Submodule.add_mem _ hu hv
    · intro c u _ hu
      have H : basisBivector Q i * (c • u) - (c • u) * basisBivector Q i = c • (basisBivector Q i * u - u * basisBivector Q i) := by
        calc basisBivector Q i * (c • u) - (c • u) * basisBivector Q i
          _ = c • (basisBivector Q i * u) - c • (u * basisBivector Q i) := by rw [Algebra.mul_smul_comm, Algebra.smul_mul_assoc]
          _ = c • (basisBivector Q i * u - u * basisBivector Q i) := by rw [smul_sub]
      rw [H]
      exact Submodule.smul_mem _ c hu
  · simp only [zero_mul, mul_zero, sub_zero, Submodule.zero_mem]
  · intro u v _ _ hu hv
    have H : (u + v) * y - y * (u + v) = (u * y - y * u) + (v * y - y * v) := by
      calc (u + v) * y - y * (u + v)
        _ = u * y + v * y - (y * u + y * v) := by rw [add_mul, mul_add]
        _ = (u * y - y * u) + (v * y - y * v) := by abel
    rw [H]
    exact Submodule.add_mem _ hu hv
  · intro c u _ hu
    have H : (c • u) * y - y * (c • u) = c • (u * y - y * u) := by
      calc (c • u) * y - y * (c • u)
        _ = c • (u * y) - c • (y * u) := by rw [Algebra.smul_mul_assoc, Algebra.mul_smul_comm]
        _ = c • (u * y - y * u) := by rw [smul_sub]
    rw [H]
    exact Submodule.smul_mem _ c hu

end InfoGeometry.Canonical.HestenesBivectorCarrier
