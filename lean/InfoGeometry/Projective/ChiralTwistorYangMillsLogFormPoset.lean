/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Tactic
import InfoGeometry.Projective.Clifford22MatrixCore
import InfoGeometry.Projective.Clifford22ChiralSpinorPositiveChart

namespace ChiralTwistorYangMillsLogFormPoset

open Clifford22
open Clifford22.Mat4

universe u

variable {R : Type u} [CommRing R]

/-! ### Projector algebra -/

theorem Pi_plus_2_add_Pi_minus_2 :
    (Pi_plus_2 : Mat4 R) + Pi_minus_2 = smul 2 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Pi_plus_2, Pi_minus_2, omega_eq, smul, Matrix.diagonal,
      Fin.sum_univ_four, zero_mul, mul_zero]
    <;> ring

theorem Pi_minus_2_mul_Pi_plus_2 :
    (Pi_minus_2 : Mat4 R) * Pi_plus_2 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Pi_plus_2, Pi_minus_2, omega_eq, Matrix.mul_apply, Fin.sum_univ_four,
      Matrix.diagonal, zero_mul, mul_zero]
    <;> ring

/-! ### Two explicit rank-one nilpotent chirality witnesses -/

def rankOneSelfDualBivector : Mat4 R := clBivec (1 : R) 1 0 0 (-1) (-1)

def rankOneAntiSelfDualBivector : Mat4 R := clBivec (1 : R) 1 0 0 1 1

theorem rankOneSelfDualBivector_sq_zero :
    rankOneSelfDualBivector (R := R) * rankOneSelfDualBivector (R := R) =
      (0 : Mat4 R) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rankOneSelfDualBivector, clBivec, E12, E13, E14, E23, E24, E34,
      E1, E2, E3, E4, smul, Matrix.mul_apply, Fin.sum_univ_four,
      Fin.ext_iff, zero_mul, mul_zero]
    <;> omega

theorem rankOneAntiSelfDualBivector_sq_zero :
    rankOneAntiSelfDualBivector (R := R) * rankOneAntiSelfDualBivector (R := R) =
      (0 : Mat4 R) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rankOneAntiSelfDualBivector, clBivec, E12, E13, E14, E23, E24, E34,
      E1, E2, E3, E4, smul, Matrix.mul_apply, Fin.sum_univ_four,
      Fin.ext_iff, zero_mul, mul_zero]
    <;> omega

theorem rankOneSelfDualBivector_selfDual :
    Pi_minus_2 (R := R) * rankOneSelfDualBivector (R := R) =
      (0 : Mat4 R) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Pi_minus_2, omega_eq, smul, rankOneSelfDualBivector, clBivec, E12,
      E13, E14, E23, E24, E34, E1, E2, E3, E4, Matrix.mul_apply,
      Fin.sum_univ_four, Matrix.diagonal, Matrix.sub_apply, Matrix.one_apply,
      zero_mul, mul_zero]
    <;> omega

theorem rankOneAntiSelfDualBivector_antiSelfDual :
    Pi_plus_2 (R := R) * rankOneAntiSelfDualBivector (R := R) =
      (0 : Mat4 R) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Pi_plus_2, omega_eq, smul, rankOneAntiSelfDualBivector, clBivec,
      E12, E13, E14, E23, E24, E34, E1, E2, E3, E4, Matrix.mul_apply,
      Fin.sum_univ_four, Matrix.diagonal, Matrix.add_apply,
      Matrix.one_apply, zero_mul, mul_zero]
    <;> omega

theorem rankOneSelfDualBivector_chiral_eigen :
    Pi_plus_2 * rankOneSelfDualBivector = smul (2 : R) rankOneSelfDualBivector := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Pi_plus_2, omega_eq, smul, rankOneSelfDualBivector, clBivec, E12,
      E13, E14, E23, E24, E34, E1, E2, E3, E4, Matrix.mul_apply,
      Fin.sum_univ_four, Matrix.diagonal, Matrix.add_apply,
      Matrix.one_apply, zero_mul, mul_zero]
    <;> ring

theorem rankOneAntiSelfDualBivector_chiral_eigen :
    Pi_minus_2 * rankOneAntiSelfDualBivector = smul (2 : R) rankOneAntiSelfDualBivector := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Pi_minus_2, omega_eq, smul, rankOneAntiSelfDualBivector, clBivec,
      E12, E13, E14, E23, E24, E34, E1, E2, E3, E4, Matrix.mul_apply,
      Fin.sum_univ_four, Matrix.diagonal, Matrix.sub_apply,
      Matrix.one_apply, zero_mul, mul_zero]
    <;> ring

theorem rankOneSelfDualBivector_real_ne_zero :
    rankOneSelfDualBivector (R := ℝ) ≠ 0 := by
  intro h
  have h₀₁ := congrFun (congrFun h (0 : Fin 4)) (1 : Fin 4)
  norm_num [rankOneSelfDualBivector, clBivec, E12, E13, E14, E23, E24, E34,
    E1, E2, E3, E4, smul, Matrix.mul_apply] at h₀₁

theorem rankOneAntiSelfDualBivector_real_ne_zero :
    rankOneAntiSelfDualBivector (R := ℝ) ≠ 0 := by
  intro h
  have h₂₃ := congrFun (congrFun h (2 : Fin 4)) (3 : Fin 4)
  norm_num [rankOneAntiSelfDualBivector, clBivec, E12, E13, E14, E23, E24, E34,
    E1, E2, E3, E4, smul, Matrix.mul_apply] at h₂₃

private theorem rankOneSelfDualBivector_eq_single :
    rankOneSelfDualBivector (R := ℝ) =
      Matrix.single (0 : Fin 4) (1 : Fin 4) (4 : ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [rankOneSelfDualBivector, clBivec, E12, E13, E14, E23, E24, E34,
      E1, E2, E3, E4, smul, Matrix.single, Matrix.mul_apply]

private theorem rankOneAntiSelfDualBivector_eq_single :
    rankOneAntiSelfDualBivector (R := ℝ) =
      Matrix.single (2 : Fin 4) (3 : Fin 4) (4 : ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [rankOneAntiSelfDualBivector, clBivec, E12, E13, E14, E23, E24, E34,
      E1, E2, E3, E4, smul, Matrix.single, Matrix.mul_apply]

/-- The self-dual nilpotent witness has actual rank one as a real `4 × 4` matrix. -/
theorem rankOneSelfDualBivector_rank :
    (rankOneSelfDualBivector (R := ℝ)).rank = 1 := by
  let w : Fin 4 → ℝ := Pi.single 0 4
  let v : Fin 4 → ℝ := Pi.single 1 1
  have hrepr : rankOneSelfDualBivector (R := ℝ) = Matrix.vecMulVec w v := by
    rw [rankOneSelfDualBivector_eq_single]
    ext i j
    by_cases hi : i = 0 <;> by_cases hj : j = 1 <;>
      simp [Matrix.vecMulVec, Matrix.single, w, v, Pi.single_apply, hi, hj, eq_comm]
  have hle : (rankOneSelfDualBivector (R := ℝ)).rank ≤ 1 := by
    rw [hrepr]
    exact Matrix.rank_vecMulVec_le w v
  have hne : (rankOneSelfDualBivector (R := ℝ)).rank ≠ 0 := by
    intro hz
    have hrange : LinearMap.range
        (rankOneSelfDualBivector (R := ℝ)).mulVecLin = ⊥ :=
      Submodule.finrank_eq_zero.mp hz
    have hmap := LinearMap.range_eq_bot.mp hrange
    have hentry := congrFun
      (congrArg (fun f => f (Pi.single (1 : Fin 4) 1)) hmap) (0 : Fin 4)
    have hzero : (4 : ℝ) = 0 := by
      simpa [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct,
        rankOneSelfDualBivector_eq_single, Matrix.single, Pi.single_apply] using hentry
    norm_num at hzero
  omega

/-- The anti-self-dual nilpotent witness has actual rank one as a real `4 × 4` matrix. -/
theorem rankOneAntiSelfDualBivector_rank :
    (rankOneAntiSelfDualBivector (R := ℝ)).rank = 1 := by
  let w : Fin 4 → ℝ := Pi.single 2 4
  let v : Fin 4 → ℝ := Pi.single 3 1
  have hrepr : rankOneAntiSelfDualBivector (R := ℝ) = Matrix.vecMulVec w v := by
    rw [rankOneAntiSelfDualBivector_eq_single]
    ext i j
    by_cases hi : i = 2 <;> by_cases hj : j = 3 <;>
      simp [Matrix.vecMulVec, Matrix.single, w, v, Pi.single_apply, hi, hj, eq_comm]
  have hle : (rankOneAntiSelfDualBivector (R := ℝ)).rank ≤ 1 := by
    rw [hrepr]
    exact Matrix.rank_vecMulVec_le w v
  have hne : (rankOneAntiSelfDualBivector (R := ℝ)).rank ≠ 0 := by
    intro hz
    have hrange : LinearMap.range
        (rankOneAntiSelfDualBivector (R := ℝ)).mulVecLin = ⊥ :=
      Submodule.finrank_eq_zero.mp hz
    have hmap := LinearMap.range_eq_bot.mp hrange
    have hzero := congrArg (fun f => f (Pi.single (3 : Fin 4) 1)) hmap
    have hentry := congrFun hzero (2 : Fin 4)
    norm_num [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct,
      rankOneAntiSelfDualBivector_eq_single, Matrix.single, Pi.single_apply] at hentry
  omega

end ChiralTwistorYangMillsLogFormPoset
