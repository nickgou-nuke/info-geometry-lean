/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib

/-! Exact parameter and generator boundaries for the proposed hyperbolic
Peirce motion. The witnesses use actual noncommuting rational matrices. -/
namespace InfoGeometry.Canonical.HyperbolicParameterBoundary

theorem integer_hyperbola_iff (u v : ℤ) :
    u * u - v * v = 1 ↔ (u = 1 ∨ u = -1) ∧ v = 0 := by
  have hf : u * u - v * v = (u - v) * (u + v) := by ring
  rw [hf, Int.mul_eq_one_iff_eq_one_or_neg_one]
  omega

abbrev Mat2Q := Matrix (Fin 2) (Fin 2) ℚ
def d : Mat2Q := !![0, 1; 0, 0]
def b : Mat2Q := !![0, 0; 1, 0]
def boost : Mat2Q := (5 / 3 : ℚ) • 1 + (4 / 3 : ℚ) • (d + b)
def boostInv : Mat2Q := (5 / 3 : ℚ) • 1 - (4 / 3 : ℚ) • (d + b)
def ellipticCandidate : Mat2Q := (5 / 3 : ℚ) • 1 + (4 / 3 : ℚ) • (d - b)
def ellipticCandidateInv : Mat2Q := (5 / 3 : ℚ) • 1 - (4 / 3 : ℚ) • (d - b)

theorem rational_parameters : (5 / 3 : ℚ)^2 - (4 / 3 : ℚ)^2 = 1 := by norm_num

theorem seeds_noncommuting : d * b ≠ b * d := by
  intro h
  have he := congrFun (congrFun h 0) 0
  norm_num [d, b, Matrix.mul_apply, Fin.sum_univ_two] at he

theorem boost_inverse : boost * boostInv = 1 ∧ boostInv * boost = 1 := by
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [boost, boostInv, d, b, Matrix.mul_apply, Fin.sum_univ_two]

theorem elliptic_generator_not_boost_inverse :
    ellipticCandidate * ellipticCandidateInv ≠ 1 := by
  intro h
  have he := congrFun (congrFun h 0) 0
  norm_num [ellipticCandidate, ellipticCandidateInv, d, b,
    Matrix.mul_apply, Fin.sum_univ_two] at he

theorem boosted_pole_explicit :
    boost * (d * b) * boostInv = !![25/9, -20/9; 20/9, -16/9] := by
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [boost, boostInv, d, b, Matrix.mul_apply, Fin.sum_univ_two]

theorem boosted_pole_idempotent :
    IsIdempotentElem (boost * (d * b) * boostInv) := by
  rw [boosted_pole_explicit]
  change (!![25/9, -20/9; 20/9, -16/9] : Mat2Q) * _ = _
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, Fin.sum_univ_two]

theorem boosted_displacement_square :
    (boost * (d * b) * boostInv - d * b) *
      (boost * (d * b) * boostInv - d * b) = (-16/9 : ℚ) • (1 : Mat2Q) := by
  rw [boosted_pole_explicit]
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [d, b, Matrix.mul_apply, Fin.sum_univ_two]

end InfoGeometry.Canonical.HyperbolicParameterBoundary
