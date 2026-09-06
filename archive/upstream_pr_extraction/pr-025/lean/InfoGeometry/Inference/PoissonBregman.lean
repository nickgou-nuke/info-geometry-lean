/-
Copyright (c) 2024-2026 Nikolay Goutev and Dimitar Tonev.
Institute for Nuclear Research and Nuclear Energy (INRNE-BAS),
Bulgarian Academy of Sciences.

Authors: Nikolay Goutev, Dimitar Tonev
-/

import Mathlib.Analysis.SpecialFunctions.Log.Basic

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
  by_cases hy0 : y = 0
  · simp [poissonBregman, hy0, le_of_lt hlam]
  · have hypos : 0 < y := lt_of_le_of_ne hy (Ne.symm hy0)
    have hratio : 0 < lam / y := div_pos hlam hypos
    have hlog := Real.log_le_sub_one_of_pos hratio
    have hscaled : y * Real.log (lam / y) ≤ lam - y := by
      calc
        y * Real.log (lam / y) ≤ y * (lam / y - 1) :=
          mul_le_mul_of_nonneg_left hlog hy
        _ = lam - y := by field_simp
    simp only [poissonBregman, if_neg hy0]
    have hlog_ratio : Real.log (lam / y) = -Real.log (y / lam) := by
      rw [Real.log_div hlam.ne' hypos.ne', Real.log_div hypos.ne' hlam.ne']
      ring
    rw [hlog_ratio] at hscaled
    linarith

end InfoGeometry.Inference
