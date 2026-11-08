/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Analysis.LogDetSelfConcordantBarrier
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

/-!
# Intrinsic trace bounds and Dikin containment on the complex positive cone

The carrier is the full algebra of finite complex matrices.  The base point is
strictly positive, and the variation is arbitrary self-adjoint.  The inverse
square root is constructed by continuous functional calculus.  The spectral
theorem is applied internally to the normalized variation, so no diagonalizing
data or commutation hypothesis is part of the API.
-/

noncomputable section

open Matrix
open scoped BigOperators CStarAlgebra MatrixOrder Matrix.Norms.L2Operator

namespace InfoGeometry.Analysis.PositiveMatrixDikin

variable {n : Type*} [Fintype n] [DecidableEq n]

local notation "Mat" => Matrix n n ℂ

/-- The real part of the ordinary matrix trace. -/
def reTrace (A : Mat) : ℝ := (Matrix.trace A).re

/-- Unitary conjugation preserves the real trace. -/
theorem reTrace_unitary_conj (U : unitary Mat) (A : Mat) :
    reTrace (Unitary.conjStarAlgAut ℂ Mat U A) = reTrace A := by
  unfold reTrace
  congr 1
  simp only [Unitary.conjStarAlgAut_apply]
  rw [Matrix.trace_mul_comm, ← mul_assoc, Unitary.coe_star_mul_self, one_mul]

/-- The native Hermitian spectral theorem computes every trace moment. -/
theorem reTrace_pow_eq_sum_eigenvalues {B : Mat} (hB : B.IsHermitian) (k : ℕ) :
    reTrace (B ^ k) = ∑ i, hB.eigenvalues i ^ k := by
  conv_lhs => rw [hB.spectral_theorem, ← map_pow]
  rw [reTrace_unitary_conj]
  simp [reTrace, Matrix.diagonal_pow, Matrix.trace_diagonal, Function.comp_def,
    ← Complex.ofReal_pow]

/-- The trace square of an arbitrary Hermitian matrix is nonnegative. -/
theorem reTrace_sq_nonneg {B : Mat} (hB : B.IsHermitian) :
    0 ≤ reTrace (B ^ 2) := by
  rw [reTrace_pow_eq_sum_eigenvalues hB]
  exact Finset.sum_nonneg fun i _ => sq_nonneg _

/-- The first trace moment is controlled by the second, with the matrix dimension as parameter. -/
theorem sq_reTrace_le_card_mul_reTrace_sq {B : Mat} (hB : B.IsHermitian) :
    reTrace B ^ 2 ≤ (Fintype.card n : ℝ) * reTrace (B ^ 2) := by
  have htrace : reTrace B = ∑ i, hB.eigenvalues i := by
    simpa only [pow_one] using reTrace_pow_eq_sum_eigenvalues hB 1
  rw [htrace, reTrace_pow_eq_sum_eigenvalues hB]
  simpa using Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ : n => (1 : ℝ))
    hB.eigenvalues

/-- Intrinsic cubic trace bound, with no supplied spectral certificate. -/
theorem abs_reTrace_cube_le {B : Mat} (hB : B.IsHermitian) :
    |reTrace (B ^ 3)| ≤ reTrace (B ^ 2) ^ (3 / 2 : ℝ) := by
  rw [reTrace_pow_eq_sum_eigenvalues hB, reTrace_pow_eq_sum_eigenvalues hB]
  have hsum := Finset.abs_sum_le_sum_abs (fun i => hB.eigenvalues i ^ 3) Finset.univ
  simp_rw [SelfConcordant.abs_cube_eq_sq_rpow_three_halves] at hsum
  exact hsum.trans (SelfConcordant.finset_sum_rpow_three_halves_le Finset.univ
    (fun i => hB.eigenvalues i ^ 2) (fun i _ => sq_nonneg _))

/-- The operator norm is bounded by the Hilbert--Schmidt size of a Hermitian matrix. -/
theorem norm_le_sqrt_reTrace_sq {B : Mat} (hB : B.IsHermitian) :
    ‖B‖ ≤ Real.sqrt (reTrace (B ^ 2)) := by
  rw [reTrace_pow_eq_sum_eigenvalues hB]
  conv_lhs => rw [hB.spectral_theorem]
  simp only [Unitary.conjStarAlgAut_apply, ← Unitary.coe_star,
    CStarRing.norm_mul_coe_unitary, CStarRing.norm_coe_unitary_mul,
    Matrix.l2_opNorm_diagonal]
  apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2
  intro i
  simp only [Function.comp_apply, RCLike.norm_ofReal]
  exact Real.abs_le_sqrt (Finset.single_le_sum (fun j _ => sq_nonneg (hB.eigenvalues j))
    (Finset.mem_univ i))

/-- A trace-square unit ball lies in the operator-norm unit ball. -/
theorem norm_lt_one_of_reTrace_sq_lt_one {B : Mat} (hB : B.IsHermitian)
    (hsmall : reTrace (B ^ 2) < 1) : ‖B‖ < 1 := by
  apply (norm_le_sqrt_reTrace_sq hB).trans_lt
  have hroot := Real.sqrt_lt_sqrt (reTrace_sq_nonneg hB) hsmall
  simpa using hroot

/-- The canonical inverse square root of the base point. -/
def inverseSqrt (P : Mat) : Mat := P ^ (-(1 / 2) : ℝ)

/-- The full, generally noncommuting, normalized matrix variation. -/
def normalizedVariation (P H : Mat) : Mat := inverseSqrt P * H * inverseSqrt P

/-- The quadratic trace form of the inverse variation. -/
def traceQuadratic (P H : Mat) : ℝ := reTrace ((P⁻¹ * H) ^ 2)

/-- The cubic trace form of the inverse variation. -/
def traceCubic (P H : Mat) : ℝ := reTrace ((P⁻¹ * H) ^ 3)

theorem inverseSqrt_isSelfAdjoint (P : Mat) : IsSelfAdjoint (inverseSqrt P) :=
  IsSelfAdjoint.of_nonneg CFC.rpow_nonneg

theorem inverseSqrt_isUnit {P : Mat} (hP : IsStrictlyPositive P) :
    IsUnit (inverseSqrt P) :=
  hP.isUnit.cfcRpow _ hP.nonneg

/-- The chosen inverse square root squares to the actual matrix inverse. -/
theorem inverseSqrt_mul_self {P : Mat} (hP : IsStrictlyPositive P) :
    inverseSqrt P * inverseSqrt P = P⁻¹ := by
  unfold inverseSqrt
  rw [← CFC.rpow_add hP.isUnit]
  norm_num
  rw [Matrix.nonsing_inv_eq_ringInverse, CFC.inverse_eq_rpow_neg_one hP]

/-- Inverse-square-root congruence normalizes the actual positive base point. -/
theorem inverseSqrt_conjugate_self {P : Mat} (hP : IsStrictlyPositive P) :
    inverseSqrt P * P * inverseSqrt P = 1 :=
  CFC.conjugate_rpow_neg_one_half P hP

/-- The normalized variation is Hermitian without assuming that `P` and `H` commute. -/
theorem normalizedVariation_isHermitian (P : Mat) {H : Mat} (hH : IsSelfAdjoint H) :
    (normalizedVariation P H).IsHermitian := by
  have hS := inverseSqrt_isSelfAdjoint P
  simpa only [normalizedVariation, ← star_eq_conjTranspose, hS.star_eq] using
    Matrix.isHermitian_mul_mul_conjTranspose (inverseSqrt P) hH.isHermitian

/-- Cyclicity identifies the first inverse trace moment with its normalized form. -/
theorem reTrace_inv_mul_eq_normalized {P : Mat} (hP : IsStrictlyPositive P) (H : Mat) :
    reTrace (P⁻¹ * H) = reTrace (normalizedVariation P H) := by
  unfold reTrace normalizedVariation
  rw [← inverseSqrt_mul_self hP]
  exact congrArg Complex.re (Matrix.trace_mul_cycle (inverseSqrt P) H (inverseSqrt P)).symm

/-- Cyclicity identifies the inverse quadratic form with the normalized trace square. -/
theorem traceQuadratic_eq_normalized {P : Mat} (hP : IsStrictlyPositive P) (H : Mat) :
    traceQuadratic P H = reTrace (normalizedVariation P H ^ 2) := by
  unfold traceQuadratic normalizedVariation reTrace
  rw [← inverseSqrt_mul_self hP]
  apply congrArg Complex.re
  let S := inverseSqrt P
  change Matrix.trace ((S * S * H) ^ 2) = Matrix.trace ((S * H * S) ^ 2)
  calc
    Matrix.trace ((S * S * H) ^ 2) = Matrix.trace (S * (S * H * S * S * H)) := by
      simp only [pow_two, mul_assoc]
    _ = Matrix.trace ((S * H * S * S * H) * S) := Matrix.trace_mul_comm _ _
    _ = Matrix.trace ((S * H * S) ^ 2) := by simp only [pow_two, mul_assoc]

/-- Cyclicity also identifies the cubic inverse and normalized trace forms. -/
theorem traceCubic_eq_normalized {P : Mat} (hP : IsStrictlyPositive P) (H : Mat) :
    traceCubic P H = reTrace (normalizedVariation P H ^ 3) := by
  unfold traceCubic normalizedVariation reTrace
  rw [← inverseSqrt_mul_self hP]
  apply congrArg Complex.re
  let S := inverseSqrt P
  change Matrix.trace ((S * S * H) ^ 3) = Matrix.trace ((S * H * S) ^ 3)
  calc
    Matrix.trace ((S * S * H) ^ 3) =
        Matrix.trace (S * (S * H * S * S * H * S * S * H)) := by
      simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    _ = Matrix.trace ((S * H * S * S * H * S * S * H) * S) := Matrix.trace_mul_comm _ _
    _ = Matrix.trace ((S * H * S) ^ 3) := by
      simp only [pow_succ, pow_zero, one_mul, mul_assoc]

/-- The inverse trace quadratic form is nonnegative on every self-adjoint variation. -/
theorem traceQuadratic_nonneg {P H : Mat} (hP : IsStrictlyPositive P)
    (hH : IsSelfAdjoint H) : 0 ≤ traceQuadratic P H := by
  rw [traceQuadratic_eq_normalized hP]
  exact reTrace_sq_nonneg (normalizedVariation_isHermitian P hH)

/-- The quadratic form vanishes only on the zero self-adjoint variation. -/
theorem traceQuadratic_eq_zero_iff {P H : Mat} (hP : IsStrictlyPositive P)
    (hH : IsSelfAdjoint H) : traceQuadratic P H = 0 ↔ H = 0 := by
  constructor
  · intro hzero
    have hnorm := norm_le_sqrt_reTrace_sq (normalizedVariation_isHermitian P hH)
    rw [← traceQuadratic_eq_normalized hP, hzero, Real.sqrt_zero] at hnorm
    have hB : normalizedVariation P H = 0 :=
      norm_eq_zero.mp (le_antisymm hnorm (norm_nonneg _))
    have hS := inverseSqrt_isUnit hP
    have hleft : inverseSqrt P * H = 0 := hS.mul_right_cancel (by
      simpa only [zero_mul, normalizedVariation] using hB)
    exact hS.mul_left_cancel (by simpa only [mul_zero] using hleft)
  · rintro rfl
    simp [traceQuadratic, reTrace]

/-- The intrinsic noncommutative trace-form self-concordance inequality. -/
theorem abs_traceCubic_le {P H : Mat} (hP : IsStrictlyPositive P)
    (hH : IsSelfAdjoint H) :
    |traceCubic P H| ≤ traceQuadratic P H ^ (3 / 2 : ℝ) := by
  rw [traceCubic_eq_normalized hP, traceQuadratic_eq_normalized hP]
  exact abs_reTrace_cube_le (normalizedVariation_isHermitian P hH)

/-- The gradient trace bound has the native matrix dimension as barrier parameter. -/
theorem abs_reTrace_inv_mul_le_sqrt_card_mul_sqrt_traceQuadratic {P H : Mat}
    (hP : IsStrictlyPositive P) (hH : IsSelfAdjoint H) :
    |reTrace (P⁻¹ * H)| ≤ Real.sqrt (Fintype.card n : ℝ) *
      Real.sqrt (traceQuadratic P H) := by
  rw [reTrace_inv_mul_eq_normalized hP, traceQuadratic_eq_normalized hP]
  have hbound := Real.abs_le_sqrt
    (sq_reTrace_le_card_mul_reTrace_sq (normalizedVariation_isHermitian P hH))
  rwa [Real.sqrt_mul (Nat.cast_nonneg (Fintype.card n))] at hbound

/-- Every self-adjoint operator of norm below one is a strictly positive perturbation of one. -/
theorem isStrictlyPositive_one_add_of_norm_lt_one {A : Type*} [CStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A] {B : A}
    (hB : IsSelfAdjoint B) (hsmall : ‖B‖ < 1) : IsStrictlyPositive (1 + B) := by
  have hpos : IsStrictlyPositive (algebraMap ℝ A (1 - ‖B‖)) :=
    isStrictlyPositive_algebraMap (sub_pos.mpr hsmall)
  apply hpos.of_le
  calc
    algebraMap ℝ A (1 - ‖B‖) = 1 + -(algebraMap ℝ A ‖B‖) := by
      simp [sub_eq_add_neg]
    _ ≤ 1 + B := add_le_add le_rfl hB.neg_algebraMap_norm_le_self

/-- Normalization of an additive perturbation uses the same inverse square root. -/
theorem inverseSqrt_conjugate_add {P : Mat} (hP : IsStrictlyPositive P) (H : Mat) :
    inverseSqrt P * (P + H) * inverseSqrt P = 1 + normalizedVariation P H := by
  simp only [mul_add, add_mul, inverseSqrt_conjugate_self hP, normalizedVariation]

/-- Normalization sends scalar multiples of the positive base point to scalar operators. -/
theorem inverseSqrt_conjugate_smul {P : Mat} (hP : IsStrictlyPositive P) (r : ℝ) :
    inverseSqrt P * (r • P) * inverseSqrt P = algebraMap ℝ Mat r := by
  rw [mul_smul_comm, smul_mul_assoc, inverseSqrt_conjugate_self hP,
    Algebra.algebraMap_eq_smul_one]

/-- Invertible normalization both preserves and reflects the operator order. -/
theorem inverseSqrt_conjugate_le_iff {P A B : Mat} (hP : IsStrictlyPositive P) :
    inverseSqrt P * A * inverseSqrt P ≤ inverseSqrt P * B * inverseSqrt P ↔ A ≤ B := by
  calc
    (inverseSqrt P * A * inverseSqrt P ≤ inverseSqrt P * B * inverseSqrt P) ↔
        0 ≤ inverseSqrt P * B * inverseSqrt P - inverseSqrt P * A * inverseSqrt P :=
      sub_nonneg.symm
    _ ↔ 0 ≤ inverseSqrt P * (B - A) * inverseSqrt P := by rw [mul_sub, sub_mul]
    _ ↔ 0 ≤ B - A := by
      simpa only [(inverseSqrt_isSelfAdjoint P).star_eq] using
        (inverseSqrt_isUnit hP).star_right_conjugate_nonneg_iff (x := B - A)
    _ ↔ A ≤ B := sub_nonneg

/-- Two-sided Loewner bounds in the genuine Dikin radius of a full matrix variation. -/
theorem dikin_order_bounds {P H : Mat} (hP : IsStrictlyPositive P)
    (hH : IsSelfAdjoint H) :
    (1 - Real.sqrt (traceQuadratic P H)) • P ≤ P + H ∧
      P + H ≤ (1 + Real.sqrt (traceQuadratic P H)) • P := by
  let r := Real.sqrt (traceQuadratic P H)
  have hB := normalizedVariation_isHermitian P hH
  have hnorm : ‖normalizedVariation P H‖ ≤ r := by
    simpa only [r, traceQuadratic_eq_normalized hP] using norm_le_sqrt_reTrace_sq hB
  have hmap : algebraMap ℝ Mat ‖normalizedVariation P H‖ ≤ algebraMap ℝ Mat r :=
    algebraMap_mono Mat hnorm
  have hlower : -(algebraMap ℝ Mat r) ≤ normalizedVariation P H :=
    (neg_le_neg hmap).trans hB.isSelfAdjoint.neg_algebraMap_norm_le_self
  have hupper : normalizedVariation P H ≤ algebraMap ℝ Mat r :=
    hB.isSelfAdjoint.le_algebraMap_norm_self.trans hmap
  constructor
  · apply (inverseSqrt_conjugate_le_iff hP).mp
    rw [inverseSqrt_conjugate_smul hP, inverseSqrt_conjugate_add hP]
    change algebraMap ℝ Mat (1 - r) ≤ 1 + normalizedVariation P H
    rw [map_sub, map_one, sub_eq_add_neg]
    exact add_le_add le_rfl hlower
  · apply (inverseSqrt_conjugate_le_iff hP).mp
    rw [inverseSqrt_conjugate_smul hP, inverseSqrt_conjugate_add hP]
    change 1 + normalizedVariation P H ≤ algebraMap ℝ Mat (1 + r)
    rw [map_add, map_one]
    exact add_le_add le_rfl hupper

/-- The full matrix Dikin unit ellipsoid is contained in the strictly positive cone. -/
theorem isStrictlyPositive_add_of_traceQuadratic_lt_one {P H : Mat}
    (hP : IsStrictlyPositive P) (hH : IsSelfAdjoint H)
    (hsmall : traceQuadratic P H < 1) : IsStrictlyPositive (P + H) := by
  rw [traceQuadratic_eq_normalized hP] at hsmall
  have hB := normalizedVariation_isHermitian P hH
  have hpos := isStrictlyPositive_one_add_of_norm_lt_one hB.isSelfAdjoint
    (norm_lt_one_of_reTrace_sq_lt_one hB hsmall)
  rw [← inverseSqrt_conjugate_add hP] at hpos
  exact ((inverseSqrt_isUnit hP).isStrictlyPositive_iff_conjugate_of_isSelfAdjoint
    (P + H) (inverseSqrt P) (inverseSqrt_isSelfAdjoint P)).mp hpos

end InfoGeometry.Analysis.PositiveMatrixDikin
