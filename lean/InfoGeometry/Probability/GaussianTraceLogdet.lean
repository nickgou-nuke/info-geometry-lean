/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

/-
The whitening argument is adapted from StatLean/Stat-Lean,
Copyright 2024 Junwei Lu and StatLean contributors, Apache License 2.0.
Source: StatLean/Minimaxity/ForMathlib/GaussianKLMulti.lean at
e436d8a184421c2a0ed8db0b2688c6cd26a7f5a2.
https://github.com/StatLean/Stat-Lean/blob/e436d8a184421c2a0ed8db0b2688c6cd26a7f5a2/LICENSE
Modifications: extract a real-valued spectral nonnegativity theorem and use it
to remove ENNReal.ofReal clipping from the actual Gaussian KL evaluation.
-/

import InfoGeometry.Probability.GaussianKullbackLeibler

/-!
# Real-valued Gaussian trace–logdet positivity

The KL evaluation has an extended nonnegative real codomain, so its
`ENNReal.ofReal` formula alone does not establish positivity of the real
expression. This file proves positivity spectrally and obtains its exact
`toReal` evaluation. Neither result assumes covariance commutativity.
-/

open MeasureTheory ProbabilityTheory InformationTheory Matrix
open scoped ENNReal NNReal RealInnerProductSpace MatrixOrder

namespace InfoGeometry.Probability

/-- The trace–logdet Burg expression is nonnegative on every real SPD matrix. -/
theorem posDef_trace_logdet_nonneg {d : ℕ} (C : Matrix (Fin d) (Fin d) ℝ)
    (hC : C.PosDef) :
    0 ≤ C.trace - Real.log C.det - d := by
  classical
  have htrace : ∑ i, hC.1.eigenvalues i = C.trace := by
    rw [hC.1.trace_eq_sum_eigenvalues]
    simp only [RCLike.ofReal_real_eq_id, id_eq]
  have hlog : ∑ i, Real.log (hC.1.eigenvalues i) = Real.log C.det := by
    rw [hC.1.det_eq_prod_eigenvalues]
    simp only [RCLike.ofReal_real_eq_id, id_eq]
    rw [Real.log_prod (fun i _ => (hC.eigenvalues_pos i).ne')]
  have hsum : 0 ≤ ∑ i : Fin d,
      (hC.1.eigenvalues i - 1 - Real.log (hC.1.eigenvalues i)) := by
    exact Finset.sum_nonneg fun i _ =>
      sub_nonneg.mpr (Real.log_le_sub_one_of_pos (hC.eigenvalues_pos i))
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one, htrace, hlog] at hsum
  linarith

/-- The full relative covariance expression is nonnegative, even when the SPD
covariances do not commute and `B⁻¹*A` is not itself symmetric. -/
theorem relative_covariance_trace_logdet_nonneg {d : ℕ}
    (A B : Matrix (Fin d) (Fin d) ℝ) (hA : A.PosDef) (hB : B.PosDef) :
    0 ≤ Real.log B.det - Real.log A.det + (B⁻¹ * A).trace - d := by
  classical
  have hBdetU : IsUnit B.det := isUnit_iff_ne_zero.mpr hB.det_pos.ne'
  have hAdetne : A.det ≠ 0 := hA.det_pos.ne'
  have hBdetne : B.det ≠ 0 := hB.det_pos.ne'
  set R : Matrix (Fin d) (Fin d) ℝ := CFC.sqrt B⁻¹ with hR_def
  have hBinv0 : (0 : Matrix (Fin d) (Fin d) ℝ) ≤ B⁻¹ :=
    Matrix.nonneg_iff_posSemidef.mpr hB.inv.posSemidef
  have hRR : R * R = B⁻¹ := by
    rw [hR_def]
    exact CFC.sqrt_mul_sqrt_self B⁻¹ hBinv0
  have hRsa : IsSelfAdjoint R := by
    rw [hR_def]
    exact IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg B⁻¹)
  have hRtransp : Rᵀ = R := by
    have h : star R = R := hRsa
    rwa [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] at h
  have hRunit : IsUnit R := by
    rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
    intro h0
    have hsq : R.det * R.det = B⁻¹.det := by rw [← Matrix.det_mul, hRR]
    rw [h0, mul_zero] at hsq
    exact hB.inv.det_pos.ne' hsq.symm
  have hRmulVecInj : Function.Injective R.mulVec :=
    Matrix.mulVec_injective_of_isUnit hRunit
  set C : Matrix (Fin d) (Fin d) ℝ := R * A * R with hC_def
  have hC : C.PosDef := by
    rw [hC_def]
    have h := hA.conjTranspose_mul_mul_same hRmulVecInj
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial, hRtransp] at h
  have hCdetB : C.det * B.det = A.det := by
    have h1 : C.det * B.det = A.det * ((R * R).det * B.det) := by
      rw [hC_def]
      simp only [Matrix.det_mul]
      ring
    rw [h1, hRR, ← Matrix.det_mul, Matrix.nonsing_inv_mul B hBdetU,
      Matrix.det_one, mul_one]
  have hlogdetC : Real.log C.det = Real.log A.det - Real.log B.det := by
    rw [eq_div_of_mul_eq hBdetne hCdetB, Real.log_div hAdetne hBdetne]
  have htraceC : C.trace = (B⁻¹ * A).trace := by
    rw [hC_def, Matrix.trace_mul_cycle, hRR]
  have h := posDef_trace_logdet_nonneg C hC
  rw [htraceC, hlogdetC] at h
  linarith

/-- The actual centered Gaussian KL is finite for strictly positive covariances. -/
theorem klDiv_multivariateGaussian_zero_ne_top {d : ℕ}
    (A B : Matrix (Fin d) (Fin d) ℝ) (hA : A.PosDef) (hB : B.PosDef) :
    klDiv (multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) A)
      (multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) B) ≠ ⊤ := by
  rw [klDiv_multivariateGaussian_zero A B hA hB]
  exact ENNReal.ofReal_ne_top

/-- Exact real-valued covariance KL formula; no clipping remains. -/
theorem toReal_klDiv_multivariateGaussian_zero {d : ℕ}
    (A B : Matrix (Fin d) (Fin d) ℝ) (hA : A.PosDef) (hB : B.PosDef) :
    (klDiv (multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) A)
      (multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) B)).toReal
      = 2⁻¹ * (Real.log B.det - Real.log A.det + (B⁻¹ * A).trace - d) := by
  rw [klDiv_multivariateGaussian_zero A B hA hB,
    ENNReal.toReal_ofReal (mul_nonneg (by norm_num)
      (relative_covariance_trace_logdet_nonneg A B hA hB))]

end InfoGeometry.Probability
