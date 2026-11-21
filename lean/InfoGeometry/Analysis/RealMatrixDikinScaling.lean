/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Analysis.MatrixSpectralSelfConcordantBarrier
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.Normed

/-!
# Real matrix Dikin scaling and recovery of ordinary bounds

The quadratic form is the existing ordered trace form, evaluated at the
actual inverse of the base matrix. Common Weyl scaling preserves that form;
scaling only the base changes it by the inverse square of the scale.

For a positive-definite real base and a symmetric variation, the normalized
variation is constructed using native continuous functional calculus. Its Frobenius norm is the Dikin
radius. The recovery estimate retains `trace A`; neither this factor nor a
subsequent Weyl scale may be discarded in a growing family of matrices.
No two matrices are assumed to commute.
-/

noncomputable section

namespace InfoGeometry.Analysis.RealMatrixDikinScaling

open Matrix SelfConcordant
open scoped BigOperators MatrixOrder Matrix.Norms.Frobenius

variable {n : ℕ}

local notation "Mat" => Matrix (Fin n) (Fin n) ℝ

/-- The nonsingular inverse transforms contragrediently under scalar dilation. -/
theorem inverse_smul (A : Mat) {c : ℝ} (hc : c ≠ 0)
    (hA : IsUnit A.det) : (c • A)⁻¹ = c⁻¹ • A⁻¹ := by
  let : Invertible c := invertibleOfNonzero hc
  simpa only [invOf_eq_inv] using Matrix.inv_smul (A := A) c hA

/-- Base-only scaling of the full ordered real Hessian bilinear form. -/
theorem hessianPhi_base_smul (A H K : Mat) {c : ℝ} (hc : c ≠ 0)
    (hA : IsUnit A.det) :
    hessianPhi (c • A)⁻¹ H K = c⁻¹ ^ 2 * hessianPhi A⁻¹ H K := by
  rw [inverse_smul A hc hA]
  simp only [hessianPhi, smul_mul_assoc, mul_smul_comm, smul_smul,
    Matrix.trace_smul, smul_eq_mul, pow_two]

/-- The real Dikin quadratic scales by inverse square when only its base is dilated. -/
theorem hessianQuad_base_smul (A H : Mat) {c : ℝ} (hc : c ≠ 0)
    (hA : IsUnit A.det) :
    hessianQuad (c • A)⁻¹ H = c⁻¹ ^ 2 * hessianQuad A⁻¹ H := by
  simpa only [hessianQuad_eq] using hessianPhi_base_smul A H H hc hA

/-- Tangent-only scaling multiplies the Dikin quadratic by the square of the scale. -/
theorem hessianQuad_tangent_smul (A H : Mat) (c : ℝ) :
    hessianQuad A⁻¹ (c • H) = c ^ 2 * hessianQuad A⁻¹ H := by
  simp only [hessianQuad, mul_smul_comm, smul_mul_assoc, smul_smul,
    Matrix.trace_smul, smul_eq_mul, pow_two]

/-- Common Weyl scaling of the base and variation preserves the Dikin quadratic. -/
theorem hessianQuad_common_smul (A H : Mat) {c : ℝ} (hc : c ≠ 0)
    (hA : IsUnit A.det) :
    hessianQuad (c • A)⁻¹ (c • H) = hessianQuad A⁻¹ H := by
  have hprod : (c • A)⁻¹ * (c • H) = A⁻¹ * H := by
    rw [inverse_smul A hc hA]
    simp only [smul_mul_assoc, mul_smul_comm, smul_smul, mul_inv_cancel₀ hc, one_smul]
  simp only [hessianQuad, hprod]

/-- The square root of the quadratic has inverse Weyl weight under positive base-only scaling. -/
theorem sqrt_hessianQuad_base_smul (A H : Mat) {c : ℝ} (hc : 0 < c)
    (hA : IsUnit A.det) :
    Real.sqrt (hessianQuad (c • A)⁻¹ H) =
      c⁻¹ * Real.sqrt (hessianQuad A⁻¹ H) := by
  rw [hessianQuad_base_smul A H hc.ne' hA, Real.sqrt_mul (sq_nonneg _),
    Real.sqrt_sq_eq_abs, abs_of_pos (inv_pos.mpr hc)]

/-- The actual inverse-square-root congruence of a real matrix variation. -/
def normalizedVariation (A H : Mat) : Mat :=
  CFC.sqrt A⁻¹ * H * CFC.sqrt A⁻¹

/-- The normalized variation is symmetric for every symmetric tangent matrix. -/
theorem normalizedVariation_isSymm (A : Mat) {H : Mat} (hH : H.IsSymm) :
    (normalizedVariation A H).IsSymm := by
  have hS : (CFC.sqrt A⁻¹).IsSymm :=
    (Matrix.isHermitian_iff_isSymm).mp (CFC.sqrt_nonneg A⁻¹).posSemidef.isHermitian
  unfold normalizedVariation
  rw [Matrix.IsSymm]
  simp only [transpose_mul, hS.eq, hH.eq, mul_assoc]

/-- Cyclic trace identifies the existing quadratic with the constructed normalized square. -/
theorem hessianQuad_eq_trace_normalized_sq {A : Mat} (hA : A.PosDef) (H : Mat) :
    hessianQuad A⁻¹ H =
      Matrix.trace (normalizedVariation A H * normalizedVariation A H) := by
  let V : MatrixSpectral.MatrixVariationConjugation n :=
    { A_inv_sqrt := CFC.sqrt A⁻¹
      H := H
      A_inv := A⁻¹
      inv_sqrt_sq := CFC.sqrt_mul_sqrt_self A⁻¹ hA.inv.posSemidef.nonneg
      B := normalizedVariation A H
      B_def := rfl }
  exact MatrixSpectral.trace_inv_H_sq_eq_trace_B_sq V

/-- Frobenius norm and trace square agree on a real symmetric matrix. -/
theorem frobenius_norm_eq_sqrt_trace_sq {B : Mat} (hB : B.IsSymm) :
    ‖B‖ = Real.sqrt (Matrix.trace (B * B)) := by
  rw [Matrix.frobenius_norm_def, trace_sq_eq_sum_sq B hB, Real.sqrt_eq_rpow]
  simp only [Real.rpow_two, Real.norm_eq_abs, sq_abs]

/-- The genuine Dikin radius is the Frobenius norm of the normalized variation. -/
theorem sqrt_hessianQuad_eq_norm_normalized {A H : Mat}
    (hA : A.PosDef) (hH : H.IsSymm) :
    Real.sqrt (hessianQuad A⁻¹ H) = ‖normalizedVariation A H‖ := by
  rw [hessianQuad_eq_trace_normalized_sq hA H]
  exact (frobenius_norm_eq_sqrt_trace_sq (normalizedVariation_isSymm A hH)).symm

/-- In particular, no positivity of the quadratic is assumed separately. -/
theorem hessianQuad_nonneg {A H : Mat} (hA : A.PosDef) (hH : H.IsSymm) :
    0 ≤ hessianQuad A⁻¹ H := by
  rw [hessianQuad_eq_trace_normalized_sq hA H]
  exact trace_sq_nonneg _ (normalizedVariation_isSymm A hH)

/-- The constructed inverse square root is the inverse of the positive square root. -/
theorem sqrt_inverse_eq_inverse_sqrt {A : Mat} (hA : A.PosDef) :
    CFC.sqrt A⁻¹ = (CFC.sqrt A)⁻¹ :=
  hA.posSemidef.inv_sqrt.symm

/-- Undoing the normalization recovers the full, possibly noncommuting variation. -/
theorem sqrt_mul_normalized_mul_sqrt {A : Mat} (hA : A.PosDef) (H : Mat) :
    CFC.sqrt A * normalizedVariation A H * CFC.sqrt A = H := by
  have hS : IsUnit (CFC.sqrt A).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp
      ((CFC.isUnit_sqrt_iff A hA.posSemidef.nonneg).mpr hA.isUnit)
  rw [normalizedVariation, sqrt_inverse_eq_inverse_sqrt hA]
  calc
    CFC.sqrt A * ((CFC.sqrt A)⁻¹ * H * (CFC.sqrt A)⁻¹) * CFC.sqrt A =
        (CFC.sqrt A * (CFC.sqrt A)⁻¹) * H * ((CFC.sqrt A)⁻¹ * CFC.sqrt A) := by
          simp only [mul_assoc]
    _ = H := by rw [Matrix.mul_nonsing_inv _ hS, Matrix.nonsing_inv_mul _ hS,
      one_mul, mul_one]

/-- The square-root Frobenius factor is the ordinary trace, with its dimension retained. -/
theorem norm_sqrt_sq_eq_trace {A : Mat} (hA : A.PosDef) :
    ‖CFC.sqrt A‖ ^ 2 = Matrix.trace A := by
  have hS : (CFC.sqrt A).IsSymm :=
    (Matrix.isHermitian_iff_isSymm).mp (CFC.sqrt_nonneg A).posSemidef.isHermitian
  have ht : 0 ≤ Matrix.trace A := by
    rw [← CFC.sqrt_mul_sqrt_self A hA.posSemidef.nonneg]
    exact trace_sq_nonneg _ hS
  rw [frobenius_norm_eq_sqrt_trace_sq hS,
    CFC.sqrt_mul_sqrt_self A hA.posSemidef.nonneg, Real.sq_sqrt ht]

/-- An ordinary real matrix bound requires the base trace in addition to its Dikin radius. -/
theorem norm_le_trace_mul_sqrt_hessianQuad {A H : Mat}
    (hA : A.PosDef) (hH : H.IsSymm) :
    ‖H‖ ≤ Matrix.trace A * Real.sqrt (hessianQuad A⁻¹ H) := by
  calc
    ‖H‖ = ‖CFC.sqrt A * normalizedVariation A H * CFC.sqrt A‖ := by
      rw [sqrt_mul_normalized_mul_sqrt hA H]
    _ ≤ (‖CFC.sqrt A‖ * ‖normalizedVariation A H‖) * ‖CFC.sqrt A‖ :=
      (Matrix.frobenius_norm_mul _ _).trans
        (mul_le_mul_of_nonneg_right (Matrix.frobenius_norm_mul _ _) (norm_nonneg _))
    _ = ‖CFC.sqrt A‖ ^ 2 * ‖normalizedVariation A H‖ := by ring
    _ = Matrix.trace A * Real.sqrt (hessianQuad A⁻¹ H) := by
      rw [norm_sqrt_sq_eq_trace hA, sqrt_hessianQuad_eq_norm_normalized hA hH]

/-- Recovering a bound from a base-scaled ellipsoid restores the full positive scale. -/
theorem norm_le_scale_mul_trace_mul_radius {A H : Mat}
    (hA : A.PosDef) (hH : H.IsSymm) {c R : ℝ} (hc : 0 < c)
    (hR : Real.sqrt (hessianQuad (c • A)⁻¹ H) ≤ R) :
    ‖H‖ ≤ c * Matrix.trace A * R := by
  have ht : 0 ≤ Matrix.trace A := by rw [← norm_sqrt_sq_eq_trace hA]; positivity
  have hbound : Real.sqrt (hessianQuad A⁻¹ H) ≤ c * R := by
    rw [sqrt_hessianQuad_base_smul A H hc (isUnit_iff_ne_zero.mpr hA.det_pos.ne')] at hR
    have hm := mul_le_mul_of_nonneg_left hR hc.le
    simpa only [← mul_assoc, mul_inv_cancel₀ hc.ne', one_mul] using hm
  calc
    ‖H‖ ≤ Matrix.trace A * Real.sqrt (hessianQuad A⁻¹ H) :=
      norm_le_trace_mul_sqrt_hessianQuad hA hH
    _ ≤ Matrix.trace A * (c * R) := mul_le_mul_of_nonneg_left hbound ht
    _ = c * Matrix.trace A * R := by ring

/-- A constructive base scale puts every symmetric real variation inside a unit quadratic bound.
The recovery theorem above retains this scale, so this is not an absolute bound on `H`. -/
theorem explicit_scale_quadratic_lt_one {A H : Mat} (hA : A.PosDef) (hH : H.IsSymm) :
    let c := 1 + Real.sqrt (hessianQuad A⁻¹ H)
    0 < c ∧ 0 ≤ hessianQuad (c • A)⁻¹ H ∧ hessianQuad (c • A)⁻¹ H < 1 := by
  dsimp only
  have hc : 0 < 1 + Real.sqrt (hessianQuad A⁻¹ H) := by positivity
  have hdet : IsUnit A.det := isUnit_iff_ne_zero.mpr hA.det_pos.ne'
  have hnonneg : 0 ≤ hessianQuad ((1 + Real.sqrt (hessianQuad A⁻¹ H)) • A)⁻¹ H := by
    rw [hessianQuad_base_smul A H hc.ne' hdet]
    exact mul_nonneg (sq_nonneg _) (hessianQuad_nonneg hA hH)
  have hradius : Real.sqrt
      (hessianQuad ((1 + Real.sqrt (hessianQuad A⁻¹ H)) • A)⁻¹ H) < 1 := by
    rw [sqrt_hessianQuad_base_smul A H hc hdet, ← div_eq_inv_mul, div_lt_one hc]
    linarith
  refine ⟨hc, hnonneg, ?_⟩
  nlinarith [Real.sq_sqrt hnonneg, Real.sqrt_nonneg
    (hessianQuad ((1 + Real.sqrt (hessianQuad A⁻¹ H)) • A)⁻¹ H)]

end InfoGeometry.Analysis.RealMatrixDikinScaling
