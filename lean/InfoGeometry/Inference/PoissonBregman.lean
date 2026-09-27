/-
Copyright (c) 2024-2026 Nikolay Goutev and Dimitar Tonev.
Institute for Nuclear Research and Nuclear Energy (INRNE-BAS),
Bulgarian Academy of Sciences.

Authors: Nikolay Goutev, Dimitar Tonev
-/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Poisson Bregman energy

The raw-count energy used by the inference core is the scalar Poisson
Bregman divergence. The zero-count branch is explicit because `0 * log 0`
must not be delegated to an informal convention.
-/

namespace InfoGeometry.Inference

/-- Scalar Poisson Bregman divergence for an observation `y` and mean `λ`. -/
noncomputable def poissonBregman (y lam : ℝ) : ℝ :=
  if y = 0 then lam else y * Real.log (y / lam) - (y - lam)

theorem poissonBregman_zero (lam : ℝ) :
    poissonBregman 0 lam = lam := by
  simp [poissonBregman]

theorem poissonBregman_nonneg
    {y lam : ℝ} (hy : 0 ≤ y) (hlam : 0 < lam) :
    0 ≤ poissonBregman y lam := by
  rcases eq_or_lt_of_le hy with rfl | hypos
  · simp [poissonBregman, hlam.le]
  · have hlog := mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos (div_pos hlam hypos)) hypos.le
    have hlog2 : Real.log (lam / y) = -Real.log (y / lam) := by rw [← Real.log_inv, inv_div]
    have hdiv : y * (lam / y) = lam := mul_div_cancel₀ lam hypos.ne'
    simp only [poissonBregman, if_neg hypos.ne']
    rw [hlog2, mul_neg, mul_sub] at hlog
    linarith

end InfoGeometry.Inference
