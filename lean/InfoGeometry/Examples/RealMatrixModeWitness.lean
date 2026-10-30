/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.PeirceStarColimit
import Mathlib.LinearAlgebra.Matrix.IsDiag

/-!
# Dense real matrix modes and their faithful colimit images

The matrices below belong to the existing full real matrix algebra at stage
two. Their entries use the two binary tensor indices. Both the square-zero
matrix and the nonzero common-kernel matrix have no zero entries, and neither
is diagonal. The square-zero matrix fails to commute with its adjoint. Its
Gram weight has an explicit noncommuting matrix and a nonzero two-sided
annihilator.

All finite identities are proved by matrix multiplication. They are then
transported to the existing real matrix colimit; nonvanishing and
noncommutation use the faithfulness of its actual stage maps. The resulting
common zero-mode is an exact algebraic statement about three native linear
endomorphisms.
-/

noncomputable section

namespace InfoGeometry.Examples.RealMatrixModeWitness

attribute [local instance 100] LieRing.ofAssociativeRing

open InfoGeometry.Clifford.Cl11TensorTowerLimit
open InfoGeometry.Canonical.RealStarColimitUniversal

open scoped BigOperators

/-- The constant-vector projection in the full `4 × 4` real matrix stage. -/
def p : Stage 2 := fun _ _ => 1 / 4

/-- A dense square-zero matrix with its column sign given by the last tensor bit. -/
def x : Stage 2 := fun _ j => (if j.2 = 0 then 1 else -1) / 4

/-- The projection onto the first-bit sign vector. -/
def k : Stage 2 := fun i j =>
  (if i.1.2 = 0 then 1 else -1) * (if j.1.2 = 0 then 1 else -1) / 4

/-- An ordered matrix-unit direction between the constant and first-bit sign vectors. -/
def z : Stage 2 := fun _ j => (if j.1.2 = 0 then 1 else -1) / 4

theorem p_isSelfAdjoint : IsSelfAdjoint p := by
  change star p = p
  ext i j
  norm_num [p, Matrix.star_apply]

theorem p_isIdempotentElem : IsIdempotentElem p := by
  change p * p = p
  ext i j
  norm_num [p, Matrix.mul_apply, InfoGeometry.Clifford.TowerMatrix.idx_card_pow_two]

theorem x_square_zero : x * x = 0 := by
  ext i j
  change (∑ t : ((Fin 1 × Fin 2) × Fin 2), x i t * x t j) = 0
  simp only [Fintype.sum_prod_type, Fin.sum_univ_one, Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;> norm_num [x]

theorem star_x_square_zero : star x * star x = 0 := by
  simpa only [star_mul, star_zero] using congrArg star x_square_zero

theorem p_mul_x : p * x = x := by
  ext i j
  change (∑ t : ((Fin 1 × Fin 2) × Fin 2), p i t * x t j) = x i j
  simp only [Fintype.sum_prod_type, Fin.sum_univ_one, Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;> norm_num [p, x]

theorem x_mul_p : x * p = 0 := by
  ext i j
  change (∑ t : ((Fin 1 × Fin 2) × Fin 2), x i t * p t j) = 0
  simp only [Fintype.sum_prod_type, Fin.sum_univ_one, Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;> norm_num [p, x]

/-- The matrix is in the native `10` Peirce corner of a self-adjoint idempotent. -/
theorem component10_x : InfoGeometry.Core.PeirceDecomposition.component10 p x = x := by
  change p * x * (1 - p) = x
  rw [p_mul_x, mul_sub, mul_one, x_mul_p, sub_zero]

theorem x_mul_star_x : x * star x = p := by
  ext i j
  change (∑ t : ((Fin 1 × Fin 2) × Fin 2), x i t * x j t) = p i j
  simp only [Fintype.sum_prod_type, Fin.sum_univ_one, Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;> norm_num [p, x]

/-- Every matrix entry is nonzero; this is not a diagonal square-zero model. -/
theorem x_entry_ne_zero (i j : InfoGeometry.Clifford.TowerMatrix.Idx 2) : x i j ≠ 0 := by
  fin_cases i <;> fin_cases j <;> norm_num [x]

theorem x_not_isDiag : ¬ x.IsDiag := by
  intro h
  exact x_entry_ne_zero (((0 : Fin 1), 0), 0) (((0 : Fin 1), 0), 1)
    (h (i := (((0 : Fin 1), 0), 0)) (j := (((0 : Fin 1), 0), 1)) (by
      intro hindex
      have hbit : (0 : Fin 2) = 1 :=
        congrArg (fun t : ((Fin 1 × Fin 2) × Fin 2) => t.2) hindex
      norm_num at hbit))

/-- The square-zero element and its adjoint genuinely fail to commute. -/
theorem x_lie_star_x_ne_zero : ⁅x, star x⁆ ≠ 0 := by
  intro h
  have hentry := congrArg (fun a : Stage 2 => a (((0 : Fin 1), 0), 0) (((0 : Fin 1), 0), 1)) h
  change (∑ t : ((Fin 1 × Fin 2) × Fin 2), x (((0 : Fin 1), 0), 0) t * x (((0 : Fin 1), 0), 1) t) -
    (∑ t : ((Fin 1 × Fin 2) × Fin 2), x t (((0 : Fin 1), 0), 0) * x t (((0 : Fin 1), 0), 1)) = 0 at hentry
  norm_num [x, Fintype.sum_prod_type, Fin.sum_univ_one, Fin.sum_univ_two] at hentry

theorem k_isSelfAdjoint : IsSelfAdjoint k := by
  change star k = k
  ext i j
  change k j i = k i j
  fin_cases i <;> fin_cases j <;> norm_num [k]

theorem k_isIdempotentElem : IsIdempotentElem k := by
  change k * k = k
  ext i j
  change (∑ t : ((Fin 1 × Fin 2) × Fin 2), k i t * k t j) = k i j
  simp only [Fintype.sum_prod_type, Fin.sum_univ_one, Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;> norm_num [k]

theorem k_entry_ne_zero (i j : InfoGeometry.Clifford.TowerMatrix.Idx 2) : k i j ≠ 0 := by
  fin_cases i <;> fin_cases j <;> norm_num [k]

theorem k_ne_zero : k ≠ 0 := by
  intro h
  apply k_entry_ne_zero (((0 : Fin 1), 0), 0) (((0 : Fin 1), 0), 0)
  exact congrArg (fun a : Stage 2 => a (((0 : Fin 1), 0), 0) (((0 : Fin 1), 0), 0)) h

theorem k_not_isDiag : ¬ k.IsDiag := by
  intro h
  exact k_entry_ne_zero (((0 : Fin 1), 0), 0) (((0 : Fin 1), 0), 1)
    (h (i := (((0 : Fin 1), 0), 0)) (j := (((0 : Fin 1), 0), 1)) (by
      intro hindex
      have hbit : (0 : Fin 2) = 1 :=
        congrArg (fun t : ((Fin 1 × Fin 2) × Fin 2) => t.2) hindex
      norm_num at hbit))

theorem x_mul_k : x * k = 0 := by
  ext i j
  change (∑ t : ((Fin 1 × Fin 2) × Fin 2), x i t * k t j) = 0
  simp only [Fintype.sum_prod_type, Fin.sum_univ_one, Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;> norm_num [x, k]

theorem star_x_mul_k : star x * k = 0 := by
  ext i j
  change (∑ t : ((Fin 1 × Fin 2) × Fin 2), x t i * k t j) = 0
  simp only [Fintype.sum_prod_type, Fin.sum_univ_one, Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;> norm_num [x, k]

theorem k_mul_x : k * x = 0 := by
  simpa only [star_mul, star_star, k_isSelfAdjoint.star_eq, star_zero] using
    congrArg star star_x_mul_k

theorem k_mul_star_x : k * star x = 0 := by
  simpa only [star_mul, k_isSelfAdjoint.star_eq, star_zero] using congrArg star x_mul_k

theorem weight_mul_k : (x * star x + star x * x) * k = 0 := by
  rw [add_mul, mul_assoc, mul_assoc, star_x_mul_k, x_mul_k,
    mul_zero, mul_zero, add_zero]

theorem k_mul_weight : k * (x * star x + star x * x) = 0 := by
  rw [mul_add, ← mul_assoc, ← mul_assoc, k_mul_x, k_mul_star_x,
    zero_mul, zero_mul, add_zero]

/-- A nonzero matrix annihilator obstructs invertibility of the Gram weight. -/
theorem weight_not_isUnit : ¬ IsUnit (x * star x + star x * x) := by
  intro h
  apply k_ne_zero
  apply h.mul_left_cancel
  simpa only [mul_zero] using weight_mul_k

/-- Native real-matrix semidefiniteness coexists with this nonzero annihilator. -/
theorem weight_posSemidef : Matrix.PosSemidef (x * star x + star x * x) :=
  InfoGeometry.Canonical.PeirceStarColimit.stage_gram_posSemidef 2 x

/-- The concrete Gram weight is not positive definite. -/
theorem weight_not_posDef : ¬ Matrix.PosDef (x * star x + star x * x) := by
  intro h
  exact weight_not_isUnit h.isUnit

theorem x_lie_k : ⁅x, k⁆ = 0 := by
  rw [Ring.lie_def, x_mul_k, k_mul_x, sub_self]

theorem star_x_lie_k : ⁅star x, k⁆ = 0 := by
  rw [Ring.lie_def, star_x_mul_k, k_mul_star_x, sub_self]

/-- The same nonzero nondiagonal matrix is annihilated by all three native
endomorphisms, using the actual ordered matrix products. -/
theorem k_common_kernel :
    (-((LieAlgebra.ad ℝ (Stage 2) (x + star x)) ^ 2)) k = 0 ∧
      ((LieAlgebra.ad ℝ (Stage 2) (x - star x)) ^ 2) k = 0 ∧
      (-(LieAlgebra.ad ℝ (Stage 2) x * LieAlgebra.ad ℝ (Stage 2) (star x) +
        LieAlgebra.ad ℝ (Stage 2) (star x) * LieAlgebra.ad ℝ (Stage 2) x)) k = 0 := by
  have hsum : ⁅x + star x, k⁆ = 0 := by
    rw [add_lie, x_lie_k, star_x_lie_k, add_zero]
  have hdifference : ⁅x - star x, k⁆ = 0 := by
    rw [sub_lie, x_lie_k, star_x_lie_k, sub_self]
  refine ⟨?_, ?_, ?_⟩
  · simp only [pow_two]
    change -⁅x + star x, ⁅x + star x, k⁆⁆ = 0
    rw [hsum, lie_zero, neg_zero]
  · simp only [pow_two]
    change ⁅x - star x, ⁅x - star x, k⁆⁆ = 0
    rw [hdifference, lie_zero]
  · change -(⁅x, ⁅star x, k⁆⁆ + ⁅star x, ⁅x, k⁆⁆) = 0
    rw [star_x_lie_k, x_lie_k, lie_zero, lie_zero, add_zero, neg_zero]

theorem z_ne_zero : z ≠ 0 := by
  intro h
  have hentry := congrArg (fun a : Stage 2 => a (((0 : Fin 1), 0), 0) (((0 : Fin 1), 0), 0)) h
  change (1 / 4 : ℝ) = 0 at hentry
  norm_num at hentry

theorem p_mul_z : p * z = z := by
  ext i j
  change (∑ t : ((Fin 1 × Fin 2) × Fin 2), p i t * z t j) = z i j
  simp only [Fintype.sum_prod_type, Fin.sum_univ_one, Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;> norm_num [p, z]

theorem x_mul_z : x * z = 0 := by
  ext i j
  change (∑ t : ((Fin 1 × Fin 2) × Fin 2), x i t * z t j) = 0
  simp only [Fintype.sum_prod_type, Fin.sum_univ_one, Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;> norm_num [x, z]

theorem z_mul_x : z * x = 0 := by
  ext i j
  change (∑ t : ((Fin 1 × Fin 2) × Fin 2), z i t * x t j) = 0
  simp only [Fintype.sum_prod_type, Fin.sum_univ_one, Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;> norm_num [x, z]

theorem z_mul_star_x : z * star x = 0 := by
  ext i j
  change (∑ t : ((Fin 1 × Fin 2) × Fin 2), z i t * x j t) = 0
  simp only [Fintype.sum_prod_type, Fin.sum_univ_one, Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;> norm_num [x, z]

theorem weight_mul_z : (x * star x + star x * x) * z = z := by
  rw [add_mul, x_mul_star_x, p_mul_z, mul_assoc, x_mul_z, mul_zero, add_zero]

theorem z_mul_weight : z * (x * star x + star x * x) = 0 := by
  rw [mul_add, ← mul_assoc, ← mul_assoc, z_mul_x, z_mul_star_x,
    zero_mul, zero_mul, add_zero]

theorem weight_lie_z : ⁅x * star x + star x * x, z⁆ = z := by
  rw [Ring.lie_def, weight_mul_z, z_mul_weight, sub_zero]

/-- The Gram weight is not ambient central in the full matrix algebra. -/
theorem weight_not_commute_z : ¬ Commute (x * star x + star x * x) z := by
  intro h
  have hmul := h.eq
  rw [weight_mul_z, z_mul_weight] at hmul
  exact z_ne_zero hmul

theorem weight_not_isDiag : ¬ (x * star x + star x * x).IsDiag := by
  intro h
  have hentry := h (i := (((0 : Fin 1), 0), 0)) (j := (((0 : Fin 1), 1), 0)) (by
    intro hindex
    have hbit : (0 : Fin 2) = 1 :=
      congrArg (fun t : ((Fin 1 × Fin 2) × Fin 2) => t.1.2) hindex
    norm_num at hbit)
  change (∑ t : ((Fin 1 × Fin 2) × Fin 2), x (((0 : Fin 1), 0), 0) t * x (((0 : Fin 1), 1), 0) t) +
    (∑ t : ((Fin 1 × Fin 2) × Fin 2), x t (((0 : Fin 1), 0), 0) * x t (((0 : Fin 1), 1), 0)) = 0 at hentry
  norm_num [x, Fintype.sum_prod_type, Fin.sum_univ_one, Fin.sum_univ_two] at hentry

section FaithfulColimit

theorem limit_x_square_zero : ofStage 2 x * ofStage 2 x = 0 :=
  limit_square_zero x_square_zero

theorem limit_k_ne_zero : ofStage 2 k ≠ 0 := by
  exact fun h => k_ne_zero ((ofStage_eq_zero_iff 2 k).mp h)

theorem limit_z_ne_zero : ofStage 2 z ≠ 0 := by
  exact fun h => z_ne_zero ((ofStage_eq_zero_iff 2 z).mp h)

/-- Faithfulness prevents the original noncommuting pair from collapsing. -/
theorem limit_x_lie_star_x_ne_zero : ⁅ofStage 2 x, star (ofStage 2 x)⁆ ≠ 0 := by
  rw [← ofStage_star]
  exact (ofStage_bracket_ne_zero_iff 2 x (star x)).mpr x_lie_star_x_ne_zero

theorem limit_x_mul_k : ofStage 2 x * ofStage 2 k = 0 := by
  simpa only [map_mul, map_zero] using congrArg (ofStage 2) x_mul_k

theorem limit_k_mul_x : ofStage 2 k * ofStage 2 x = 0 := by
  simpa only [map_mul, map_zero] using congrArg (ofStage 2) k_mul_x

theorem limit_star_x_mul_k : star (ofStage 2 x) * ofStage 2 k = 0 := by
  simpa only [map_mul, map_zero, ofStage_star] using congrArg (ofStage 2) star_x_mul_k

theorem limit_k_mul_star_x : ofStage 2 k * star (ofStage 2 x) = 0 := by
  simpa only [map_mul, map_zero, ofStage_star] using congrArg (ofStage 2) k_mul_star_x

theorem limit_weight_mul_k :
    (ofStage 2 x * star (ofStage 2 x) + star (ofStage 2 x) * ofStage 2 x) *
      ofStage 2 k = 0 := by
  simpa only [map_mul, map_add, map_zero, ofStage_star] using
    congrArg (ofStage 2) weight_mul_k

theorem limit_k_mul_weight :
    ofStage 2 k *
      (ofStage 2 x * star (ofStage 2 x) + star (ofStage 2 x) * ofStage 2 x) = 0 := by
  simpa only [map_mul, map_add, map_zero, ofStage_star] using
    congrArg (ofStage 2) k_mul_weight

/-- The nonzero annihilator survives faithful inclusion, so the Gram weight
is not a unit in the existing real matrix colimit either. -/
theorem limit_weight_not_isUnit :
    ¬ IsUnit (ofStage 2 x * star (ofStage 2 x) +
      star (ofStage 2 x) * ofStage 2 x) := by
  intro h
  apply limit_k_ne_zero
  apply h.mul_left_cancel
  simpa only [mul_zero] using limit_weight_mul_k

theorem limit_weight_mul_z :
    (ofStage 2 x * star (ofStage 2 x) + star (ofStage 2 x) * ofStage 2 x) *
      ofStage 2 z = ofStage 2 z := by
  simpa only [map_mul, map_add, ofStage_star] using congrArg (ofStage 2) weight_mul_z

theorem limit_z_mul_weight :
    ofStage 2 z *
      (ofStage 2 x * star (ofStage 2 x) + star (ofStage 2 x) * ofStage 2 x) = 0 := by
  simpa only [map_mul, map_add, map_zero, ofStage_star] using
    congrArg (ofStage 2) z_mul_weight

/-- The Gram weight remains noncentral in the actual faithful colimit. -/
theorem limit_weight_not_commute_z :
    ¬ Commute (ofStage 2 x * star (ofStage 2 x) +
      star (ofStage 2 x) * ofStage 2 x) (ofStage 2 z) := by
  intro h
  have hmul := h.eq
  rw [limit_weight_mul_z, limit_z_mul_weight] at hmul
  exact limit_z_ne_zero hmul

/-- The same faithful image is a common zero-mode of all three native
endomorphisms of the existing real matrix colimit. -/
theorem limit_k_common_kernel :
    (-((LieAlgebra.ad ℝ Limit (ofStage 2 x + star (ofStage 2 x))) ^ 2))
        (ofStage 2 k) = 0 ∧
      ((LieAlgebra.ad ℝ Limit (ofStage 2 x - star (ofStage 2 x))) ^ 2)
        (ofStage 2 k) = 0 ∧
      (-(LieAlgebra.ad ℝ Limit (ofStage 2 x) *
          LieAlgebra.ad ℝ Limit (star (ofStage 2 x)) +
        LieAlgebra.ad ℝ Limit (star (ofStage 2 x)) *
          LieAlgebra.ad ℝ Limit (ofStage 2 x))) (ofStage 2 k) = 0 := by
  have hleft : ⁅ofStage 2 x, ofStage 2 k⁆ = 0 := by
    rw [Ring.lie_def, limit_x_mul_k, limit_k_mul_x, sub_self]
  have hright : ⁅star (ofStage 2 x), ofStage 2 k⁆ = 0 := by
    rw [Ring.lie_def, limit_star_x_mul_k, limit_k_mul_star_x, sub_self]
  have hsum : ⁅ofStage 2 x + star (ofStage 2 x), ofStage 2 k⁆ = 0 := by
    rw [add_lie, hleft, hright, add_zero]
  have hdifference : ⁅ofStage 2 x - star (ofStage 2 x), ofStage 2 k⁆ = 0 := by
    rw [sub_lie, hleft, hright, sub_self]
  refine ⟨?_, ?_, ?_⟩
  · simp only [pow_two]
    change -⁅ofStage 2 x + star (ofStage 2 x),
      ⁅ofStage 2 x + star (ofStage 2 x), ofStage 2 k⁆⁆ = 0
    rw [hsum, lie_zero, neg_zero]
  · simp only [pow_two]
    change ⁅ofStage 2 x - star (ofStage 2 x),
      ⁅ofStage 2 x - star (ofStage 2 x), ofStage 2 k⁆⁆ = 0
    rw [hdifference, lie_zero]
  · change -(⁅ofStage 2 x, ⁅star (ofStage 2 x), ofStage 2 k⁆⁆ +
      ⁅star (ofStage 2 x), ⁅ofStage 2 x, ofStage 2 k⁆⁆) = 0
    rw [hright, hleft, lie_zero, lie_zero, add_zero, neg_zero]

end FaithfulColimit

end InfoGeometry.Examples.RealMatrixModeWitness
