/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Routing.BlockCausalSinkhorn

/-!
# Compatibility of the two finite Sinkhorn branch APIs

The iterations and gains agree exactly. This does not identify a raw detector
readout with a normalized responsibility readout, or assert convergence.
-/

namespace InfoGeometry.Routing.BlockCausalSinkhorn
open scoped BigOperators
variable {K : Type*} [Fintype K]

theorem logSumExp_eq_logsumexp (a : K → ℝ) :
    logSumExp a = FiniteLogSinkhorn.logsumexp a := by
  simp [logSumExp, FiniteLogSinkhorn.logsumexp, FiniteSoftmax.partitionZ]

theorem potentials_eq_sinkhornPotentials (S : Matrix K K ℝ) (T : ℕ) :
    potentials S T = FiniteLogSinkhorn.sinkhornPotentials S T := by
  induction T with
  | zero => rfl
  | succ T ih =>
    simp only [potentials, FiniteLogSinkhorn.sinkhornPotentials,
      logSumExp_eq_logsumexp] at ih ⊢
    rw [ih]

theorem core_eq_sinkhornMatrix (S : Matrix K K ℝ) (T : ℕ) :
    core S T = FiniteLogSinkhorn.sinkhornMatrix T S := by
  unfold InfoGeometry.Routing.BlockCausalSinkhorn.core FiniteLogSinkhorn.sinkhornMatrix
  rw [potentials_eq_sinkhornPotentials]

theorem gauge_eq_sinkhornGaugeShift (S : Matrix K K ℝ) (T : ℕ) :
    gauge S T = FiniteLogSinkhorn.sinkhornGaugeShift
      (FiniteLogSinkhorn.sinkhornPotentials S T) := by
  simp only [gauge, FiniteLogSinkhorn.sinkhornGaugeShift,
    potentials_eq_sinkhornPotentials, div_eq_mul_inv, mul_comm]

theorem exp_logShapeGain_eq (S : Matrix K K ℝ) (T : ℕ) (i : K) :
    Real.exp (logShapeGain S T i) = FiniteLogSinkhorn.sinkhornShapeGain T S i := by
  simp only [logShapeGain, FiniteLogSinkhorn.sinkhornShapeGain,
    potentials_eq_sinkhornPotentials, gauge_eq_sinkhornGaugeShift]

theorem exp_logDetectorGain_eq (S : Matrix K K ℝ) (T : ℕ) (i : K) :
    Real.exp (logDetectorGain S T i) = FiniteLogSinkhorn.sinkhornDetGain T S i := by
  simp only [logDetectorGain, FiniteLogSinkhorn.sinkhornDetGain,
    potentials_eq_sinkhornPotentials, gauge_eq_sinkhornGaugeShift]

end InfoGeometry.Routing.BlockCausalSinkhorn
