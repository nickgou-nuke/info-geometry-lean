/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.LieJordanGeneratorTrace
import InfoGeometry.Canonical.RealLieJordanGeometry
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add

/-!
# Dense real witnesses and an exact nonpositive generator orbit

Every operator acts on the full real matrix algebra. The dense projection and
seed give noncommuting opposite corners. Exact entries refute normalization
claims; an actual matrix quadratic form refutes positivity along an affine
solution of the skew-plus generator equation. Transpose and reflection-metric
transpose remain distinct on this same real carrier.
-/

namespace InfoGeometry.Canonical.RealLieJordanExamples

open Matrix Core.PeirceDecomposition Core.PeirceGrading Core.PeirceCoupledCorners
open Core.PeirceSandwichDuality Core.LieJordanGenerators LieJordanGeneratorTrace
open scoped Matrix InfoGeometry.Canonical.RealLieJordanGeometry

attribute [local instance 100] LieRing.ofAssociativeRing

noncomputable section

abbrev Mat3 := Matrix (Fin 3) (Fin 3) ℝ

def P : Mat3 := fun _ _ => 1 / 3
def S : Mat3 := !![1, 2, 3; 2, 4, 5; 3, 5, 6]
def U : Mat3 := component10 P S
def probe : Fin 3 → ℝ := ![-13, 2, 11]

theorem P_idempotent : IsIdempotentElem P := by
  change P * P = P
  ext i j
  norm_num [P, Matrix.mul_apply, Fin.sum_univ_succ]

theorem P_transpose : P.transpose = P := by
  ext i j
  rfl

theorem S_transpose : S.transpose = S := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [S, Matrix.transpose_apply]

theorem P_isStarProjection : IsStarProjection P := by
  refine ⟨P_idempotent, ?_⟩
  simpa only [IsSelfAdjoint, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_eq_transpose_of_trivial] using P_transpose

theorem P_posSemidef : P.PosSemidef := by
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial,
    P_transpose, P_idempotent.eq] using Matrix.posSemidef_self_mul_conjTranspose P

theorem P_dense (i j : Fin 3) : P i j ≠ 0 := by norm_num [P]

theorem S_dense (i j : Fin 3) : S i j ≠ 0 := by
  fin_cases i <;> fin_cases j <;> norm_num [S]

theorem P_mul_S_ne_S_mul_P : P * S ≠ S * P := by
  intro h
  have he := congrArg (fun x : Mat3 => x 0 1) h
  simp only [Matrix.mul_apply] at he
  norm_num [P, S, Fin.sum_univ_succ] at he

theorem U_apply (i j : Fin 3) : U i j = probe j / 9 := by
  fin_cases i <;> fin_cases j <;>
    simp only [U, component10, complementIdempotent, Matrix.mul_apply, Matrix.sub_apply] <;>
    norm_num [P, S, probe, Fin.sum_univ_succ, Matrix.one_apply]

theorem U_dense (i j : Fin 3) : U i j ≠ 0 := by
  rw [U_apply]
  fin_cases j <;> norm_num [probe]

theorem U_mem_peirce10 : U ∈ peirce10 P := component10_mem P S

theorem U_transpose_mem_peirce01 : U.transpose ∈ peirce01 P := by
  simpa only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
    using star_mem_peirce01 P_isStarProjection.isSelfAdjoint U_mem_peirce10

theorem gram_apply (i j : Fin 3) :
    (U * U.transpose + U.transpose * U) i j = (98 + probe i * probe j) / 27 := by
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply] <;>
    norm_num [U_apply, probe, Fin.sum_univ_succ]

theorem bracket_apply (i j : Fin 3) :
    (⁅U, U.transpose⁆ : Mat3) i j = (98 - probe i * probe j) / 27 := by
  change (U * U.transpose - U.transpose * U) i j = _
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.sub_apply, Matrix.mul_apply, Matrix.transpose_apply] <;>
    norm_num [U_apply, probe, Fin.sum_univ_succ]

theorem U_mul_transpose_ne_transpose_mul : U * U.transpose ≠ U.transpose * U := by
  intro h
  have he := congrArg (fun x : Mat3 => x 0 0) (sub_eq_zero.mpr h)
  change (⁅U, U.transpose⁆ : Mat3) 0 0 = 0 at he
  rw [bracket_apply] at he
  norm_num [probe] at he

theorem gram_square :
    (U * U.transpose + U.transpose * U) ^ 2 =
      (98 / 9 : ℝ) • (U * U.transpose + U.transpose * U) := by
  have hK : U * U.transpose + U.transpose * U =
      fun i j => (98 + probe i * probe j) / 27 := by
    ext i j
    exact gram_apply i j
  rw [hK]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [pow_two, Matrix.mul_apply, Matrix.smul_apply] <;>
    norm_num [probe, Fin.sum_univ_succ]

theorem one_sub_gram_idempotence_defect_entry :
    (((1 - (U * U.transpose + U.transpose * U)) ^ 2 -
      (1 - (U * U.transpose + U.transpose * U))) : Mat3) 0 0 = 7921 / 81 := by
  rw [one_sub_idempotence_defect, gram_square]
  simp only [Matrix.sub_apply, Matrix.smul_apply, gram_apply]
  norm_num [probe]

theorem one_sub_gram_not_idempotent :
    ¬ IsIdempotentElem (1 - (U * U.transpose + U.transpose * U)) := by
  intro h
  have he := congrArg (fun x : Mat3 => x 0 0) (sub_eq_zero.mpr h.eq)
  have hd := one_sub_gram_idempotence_defect_entry
  rw [pow_two] at hd
  rw [he] at hd
  norm_num at hd

theorem skewPlus_one_sub_gram_entry :
    (skewPlusGenerator (R := ℝ) U U.transpose
      (1 - (U * U.transpose + U.transpose * U))) 0 0 = 25276 / 243 := by
  rw [skewPlusGenerator_one_sub_quadratic P_idempotent
    U_mem_peirce10 U_transpose_mem_peirce01]
  simp only [Matrix.smul_apply, nsmul_eq_mul, Nat.cast_ofNat]
  simp only [Matrix.mul_apply, Matrix.sub_apply, bracket_apply, gram_apply]
  norm_num [bracket_apply, gram_apply, probe, Fin.sum_univ_succ, Matrix.one_apply]

theorem skewPlus_one_sub_gram_ne_zero :
    skewPlusGenerator (R := ℝ) U U.transpose
      (1 - (U * U.transpose + U.transpose * U)) ≠ 0 := by
  intro h
  have he := congrArg (fun x : Mat3 => x 0 0) h
  rw [skewPlus_one_sub_gram_entry] at he
  norm_num at he

theorem skewPlus_one_entry :
    (skewPlusGenerator (R := ℝ) U U.transpose 1) 0 0 = -284 / 27 := by
  rw [skewPlusGenerator_one]
  simp only [Matrix.smul_apply]
  norm_num [bracket_apply, probe]

theorem trace_skewMinus_projection :
    trace (skewMinusGenerator (R := ℝ) U U.transpose P) = -392 / 9 := by
  rw [trace_skewMinusGenerator]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
  norm_num [bracket_apply, P, probe, Fin.sum_univ_succ]

theorem skew_sandwich_one_entry :
    (U * 1 * U.transpose - U.transpose * 1 * U) 0 0 = -71 / 27 := by
  simp only [mul_one]
  change (⁅U, U.transpose⁆ : Mat3) 0 0 = _
  norm_num [bracket_apply, probe]

theorem skew_sandwich_one_not_posSemidef :
    ¬ (U * 1 * U.transpose - U.transpose * 1 * U).PosSemidef := by
  intro h
  have he := h.diag_nonneg (i := (0 : Fin 3))
  rw [skew_sandwich_one_entry] at he
  norm_num at he

theorem skewPlus_twice_projection :
    skewPlusGenerator (R := ℝ) U U.transpose
      (skewPlusGenerator (R := ℝ) U U.transpose P) = 0 := by
  rw [skewPlusGenerator_projection P_idempotent U_mem_peirce10 U_transpose_mem_peirce01,
    map_nsmul, skewPlusGenerator_bracket P_idempotent U_mem_peirce10 U_transpose_mem_peirce01,
    smul_zero]

def affineOrbit (t : ℝ) : Mat3 := P + t • skewPlusGenerator (R := ℝ) U U.transpose P

theorem affineOrbit_zero : affineOrbit 0 = P := by simp [affineOrbit]

theorem affineOrbit_generator (t : ℝ) :
    skewPlusGenerator (R := ℝ) U U.transpose (affineOrbit t) =
      skewPlusGenerator (R := ℝ) U U.transpose P := by
  rw [affineOrbit, map_add, map_smul, skewPlus_twice_projection, smul_zero, add_zero]

/-- The affine curve solves the actual native operator differential equation. -/
theorem affineOrbit_hasDerivAt (t : ℝ) :
    HasDerivAt affineOrbit
      (skewPlusGenerator (R := ℝ) U U.transpose (affineOrbit t)) t := by
  rw [affineOrbit_generator]
  change HasDerivAt (fun s : ℝ => P + s • skewPlusGenerator (R := ℝ) U U.transpose P)
    (skewPlusGenerator (R := ℝ) U U.transpose P) t
  simpa using HasDerivAt.const_add P
    ((hasDerivAt_id t).smul_const (skewPlusGenerator (R := ℝ) U U.transpose P))

theorem affineOrbit_quadratic_form (t : ℝ) :
    probe ⬝ᵥ (affineOrbit t *ᵥ probe) = -(19208 / 3 : ℝ) * t := by
  rw [affineOrbit, skewPlusGenerator_projection P_idempotent
    U_mem_peirce10 U_transpose_mem_peirce01]
  simp only [Matrix.mulVec, dotProduct, Matrix.add_apply, Matrix.smul_apply,
    smul_eq_mul, two_nsmul]
  norm_num [bracket_apply, P, probe, Fin.sum_univ_succ]
  ring

/-- A positive initial matrix leaves the positive cone at every positive time. -/
theorem affineOrbit_not_posSemidef {t : ℝ} (ht : 0 < t) :
    ¬ (affineOrbit t).PosSemidef := by
  intro h
  have hq := h.dotProduct_mulVec_nonneg probe
  simp only [star_trivial] at hq
  rw [affineOrbit_quadratic_form] at hq
  nlinarith

theorem reflection_transpose : (reflection P).transpose = reflection P := by
  ext i j
  simp only [reflection, two_mul, Matrix.sub_apply, Matrix.add_apply, Matrix.transpose_apply]
  norm_num [P, Matrix.one_apply, eq_comm]

theorem reflection_involutive : reflection P * reflection P = 1 := reflection_sq P_idempotent

/-- The reflection-metric transpose of this odd corner has the opposite sign. -/
theorem krein_U : reflection P * U.transpose * reflection P = -U.transpose := by
  rw [reflection_mul_corner01 P_idempotent U_transpose_mem_peirce01, neg_mul,
    corner01_mul_reflection P_idempotent U_transpose_mem_peirce01]

theorem krein_seed :
    reflection P * (reflection P * S).transpose * reflection P = reflection P * S := by
  rw [Matrix.transpose_mul, S_transpose, reflection_transpose, mul_assoc,
    mul_assoc, reflection_involutive, mul_one]

/-- The corresponding bilinear trace form is not positive definite. -/
theorem krein_U_trace : trace ((reflection P * U.transpose * reflection P) * U) = -98 / 9 := by
  rw [krein_U, neg_mul, trace_neg]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply]
  norm_num [U_apply, probe, Fin.sum_univ_succ]

end

end InfoGeometry.Canonical.RealLieJordanExamples
