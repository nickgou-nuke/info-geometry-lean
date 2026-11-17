/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.HestenesClPlus14
import Mathlib.LinearAlgebra.CliffordAlgebra.Conjugation
import Mathlib.Tactic.Module

/-! # Eight real coefficients and the full native Hestenes current

The frame is ordered as
`[1, γ₀γ₁, γ₀γ₂, γ₀γ₃, γ₂γ₃, γ₃γ₁, γ₁γ₂, γ₀γ₁γ₂γ₃]`
in the existing Mathlib Clifford algebra of signature `(+---)`.
In particular the three boost blades are the negatives of the existing
`sigmaEven` generators. The `γ₃γ₁` ordering is retained in the fifth bivector.

The synthesis map lands in the actual even subalgebra. The current identity
normalizes genuine Clifford products using the existing generator squares
and anticommutation laws; scalar polynomial collection occurs only afterward.
It identifies the entire sandwich with the image of an explicit spacetime
vector, including its spatial components and cancellation of odd grade-three
terms. No complex matrix representative, assumed Fierz identities, differential
equation, or current-conservation law is used.
-/

noncomputable section

namespace InfoGeometry.Canonical.HestenesNativeSpinorFrame

open HestenesCl14
open scoped BigOperators

/-- The eight ordered real blades, constructed inside the native even subalgebra. -/
def evenBlade : Fin 8 → ClPlus14
  | 0 => 1
  | 1 => (CliffordAlgebra.even.ι Q14).bilin (basisVec 0) (basisVec 1)
  | 2 => (CliffordAlgebra.even.ι Q14).bilin (basisVec 0) (basisVec 2)
  | 3 => (CliffordAlgebra.even.ι Q14).bilin (basisVec 0) (basisVec 3)
  | 4 => (CliffordAlgebra.even.ι Q14).bilin (basisVec 2) (basisVec 3)
  | 5 => (CliffordAlgebra.even.ι Q14).bilin (basisVec 3) (basisVec 1)
  | 6 => (CliffordAlgebra.even.ι Q14).bilin (basisVec 1) (basisVec 2)
  | 7 =>
      (CliffordAlgebra.even.ι Q14).bilin (basisVec 0) (basisVec 1) *
        (CliffordAlgebra.even.ι Q14).bilin (basisVec 2) (basisVec 3)

theorem evenBlade_val (i : Fin 8) :
    (evenBlade i : Cl14) =
      match i with
      | 0 => 1
      | 1 => gamma 0 * gamma 1
      | 2 => gamma 0 * gamma 2
      | 3 => gamma 0 * gamma 3
      | 4 => gamma 2 * gamma 3
      | 5 => gamma 3 * gamma 1
      | 6 => gamma 1 * gamma 2
      | 7 => (gamma 0 * gamma 1) * (gamma 2 * gamma 3) := by
  fin_cases i <;> rfl

/-- Real coefficient synthesis into the actual even Clifford algebra. -/
def synthesis : (Fin 8 → ℝ) →ₗ[ℝ] ClPlus14 where
  toFun c := ∑ i : Fin 8, c i • evenBlade i
  map_add' c d := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' r c := by simp [Finset.smul_sum, smul_smul]

theorem synthesis_apply (c : Fin 8 → ℝ) :
    synthesis c = ∑ i : Fin 8, c i • evenBlade i := rfl

/-- The synthesis coefficients retain the prescribed order and all eight blades. -/
theorem synthesis_val (c : Fin 8 → ℝ) :
    (synthesis c : Cl14) =
      c 0 • (1 : Cl14) +
      c 1 • (gamma 0 * gamma 1) +
      c 2 • (gamma 0 * gamma 2) +
      c 3 • (gamma 0 * gamma 3) +
      c 4 • (gamma 2 * gamma 3) +
      c 5 • (gamma 3 * gamma 1) +
      c 6 • (gamma 1 * gamma 2) +
      c 7 • ((gamma 0 * gamma 1) * (gamma 2 * gamma 3)) := by
  simp [synthesis, evenBlade, Fin.sum_univ_succ, gamma]
  <;> abel

/-- The four polynomial components of the native sandwich in the fixed frame. -/
def currentVector (c : Fin 8 → ℝ) : V14
  | 0 => ∑ i : Fin 8, c i ^ 2
  | 1 => 2 * (-(c 0 * c 1) + c 2 * c 6 - c 3 * c 5 - c 4 * c 7)
  | 2 => 2 * (-(c 0 * c 2) - c 1 * c 6 + c 3 * c 4 - c 5 * c 7)
  | 3 => 2 * (-(c 0 * c 3) + c 1 * c 5 - c 2 * c 4 - c 6 * c 7)

theorem currentVector_time (c : Fin 8 → ℝ) :
    currentVector c 0 = ∑ i : Fin 8, c i ^ 2 := rfl

/-- Expand the native vector inclusion in the existing spacetime frame. -/
theorem iota14_decomposition (v : V14) :
    ι14 v = v 0 • gamma 0 + v 1 • gamma 1 + v 2 • gamma 2 + v 3 • gamma 3 := by
  have hv : v = v 0 • basisVec 0 + v 1 • basisVec 1 +
      v 2 • basisVec 2 + v 3 • basisVec 3 := by
    ext i
    fin_cases i <;> simp [basisVec]
  calc
    ι14 v = ι14 (v 0 • basisVec 0 + v 1 • basisVec 1 +
        v 2 • basisVec 2 + v 3 • basisVec 3) := congrArg ι14 hv
    _ = _ := by simp [gamma]

private theorem reverse_gamma (i : Fin 4) :
    CliffordAlgebra.reverse (gamma i) = gamma i := by
  simp [gamma]

private theorem g10 : gamma 1 * gamma 0 = -(gamma 0 * gamma 1) :=
  eq_neg_of_add_eq_zero_left (gamma_anticomm (i := 1) (j := 0) (by decide))

private theorem g20 : gamma 2 * gamma 0 = -(gamma 0 * gamma 2) :=
  eq_neg_of_add_eq_zero_left (gamma_anticomm (i := 2) (j := 0) (by decide))

private theorem g30 : gamma 3 * gamma 0 = -(gamma 0 * gamma 3) :=
  eq_neg_of_add_eq_zero_left (gamma_anticomm (i := 3) (j := 0) (by decide))

private theorem g21 : gamma 2 * gamma 1 = -(gamma 1 * gamma 2) :=
  eq_neg_of_add_eq_zero_left (gamma_anticomm (i := 2) (j := 1) (by decide))

private theorem g31 : gamma 3 * gamma 1 = -(gamma 1 * gamma 3) :=
  eq_neg_of_add_eq_zero_left (gamma_anticomm (i := 3) (j := 1) (by decide))

private theorem g32 : gamma 3 * gamma 2 = -(gamma 2 * gamma 3) :=
  eq_neg_of_add_eq_zero_left (gamma_anticomm (i := 3) (j := 2) (by decide))

private theorem g00n (x : Cl14) : gamma 0 * (gamma 0 * x) = x := by
  rw [← mul_assoc, gamma_zero_sq, one_mul]

private theorem g11n (x : Cl14) : gamma 1 * (gamma 1 * x) = -x := by
  rw [← mul_assoc, gamma_one_sq, neg_one_mul]

private theorem g22n (x : Cl14) : gamma 2 * (gamma 2 * x) = -x := by
  rw [← mul_assoc, gamma_two_sq, neg_one_mul]

private theorem g33n (x : Cl14) : gamma 3 * (gamma 3 * x) = -x := by
  rw [← mul_assoc, gamma_three_sq, neg_one_mul]

private theorem g10n (x : Cl14) : gamma 1 * (gamma 0 * x) = -(gamma 0 * (gamma 1 * x)) := by
  rw [← mul_assoc, g10, neg_mul, mul_assoc]

private theorem g20n (x : Cl14) : gamma 2 * (gamma 0 * x) = -(gamma 0 * (gamma 2 * x)) := by
  rw [← mul_assoc, g20, neg_mul, mul_assoc]

private theorem g30n (x : Cl14) : gamma 3 * (gamma 0 * x) = -(gamma 0 * (gamma 3 * x)) := by
  rw [← mul_assoc, g30, neg_mul, mul_assoc]

private theorem g21n (x : Cl14) : gamma 2 * (gamma 1 * x) = -(gamma 1 * (gamma 2 * x)) := by
  rw [← mul_assoc, g21, neg_mul, mul_assoc]

private theorem g31n (x : Cl14) : gamma 3 * (gamma 1 * x) = -(gamma 1 * (gamma 3 * x)) := by
  rw [← mul_assoc, g31, neg_mul, mul_assoc]

private theorem g32n (x : Cl14) : gamma 3 * (gamma 2 * x) = -(gamma 2 * (gamma 3 * x)) := by
  rw [← mul_assoc, g32, neg_mul, mul_assoc]

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 4000 in
/-- The entire ordered Clifford sandwich is the native image of the displayed
spacetime vector. The proof also eliminates every grade-three component. -/
theorem synthesis_sandwich_eq_iota (c : Fin 8 → ℝ) :
    (synthesis c : Cl14) * gamma 0 * CliffordAlgebra.reverse (synthesis c : Cl14) =
      ι14 (currentVector c) := by
  simp only [synthesis_val, map_add, map_smul, CliffordAlgebra.reverse.map_one,
    CliffordAlgebra.reverse.map_mul, reverse_gamma]
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_smul]
  simp only [mul_assoc, g00n, g11n, g22n, g33n,
    g10n, g20n, g30n, g21n, g31n, g32n,
    gamma_zero_sq, gamma_one_sq, gamma_two_sq, gamma_three_sq,
    g10, g20, g30, g21, g31, g32,
    one_mul, mul_one, neg_mul, mul_neg, neg_neg, neg_one_mul, mul_neg_one, smul_neg]
  rw [iota14_decomposition (currentVector c)]
  simp [currentVector, Fin.sum_univ_succ]
  module

/-- The quadratic form of the encoded current is a sum of two real squares.
This is a consequence for the explicit current, with no assumed Fierz package. -/
theorem currentVector_quadratic (c : Fin 8 → ℝ) :
    Q14 (currentVector c) =
      (c 0 ^ 2 - c 1 ^ 2 - c 2 ^ 2 - c 3 ^ 2 + c 4 ^ 2 + c 5 ^ 2 +
        c 6 ^ 2 - c 7 ^ 2) ^ 2 +
      (2 * (c 0 * c 7 - c 1 * c 4 - c 2 * c 5 - c 3 * c 6)) ^ 2 := by
  simp [Q14_apply, currentVector, qCoeff, Fin.sum_univ_succ]
  ring

/-- Every encoded current has nonnegative Minkowski quadratic form. -/
theorem currentVector_quadratic_nonneg (c : Fin 8 → ℝ) :
    0 ≤ Q14 (currentVector c) := by
  rw [currentVector_quadratic]
  positivity

end InfoGeometry.Canonical.HestenesNativeSpinorFrame

end
