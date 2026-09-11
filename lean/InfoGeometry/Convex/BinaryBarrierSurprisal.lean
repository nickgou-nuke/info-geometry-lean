import InfoGeometry.Convex.BipolarLogitBarrierDuality
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Modular.SelfConcordantBarrierTriple
import InfoGeometry.Analysis.SpectralSurprisalLogDetBridge
import InfoGeometry.Analysis.LogOddsSimplexGeometry

/-!
# The binary log barrier, surprisal, and distinct Hessians

The interval barrier is the unweighted trace of the diagonal surprisal, whereas
Shannon entropy is its probability-weighted mean. The barrier Hessian is not
the surprisal operator or the Fisher metric. This owner connects the existing
definitions and proves a derivative-level self-concordance bound by applying
the repository's finite positive-cone theorem to the tangent `(1,-1)`.
-/

noncomputable section
namespace InfoGeometry.Convex.BinaryBarrierSurprisal

open InfoGeometry.Convex.BipolarLogitBarrierDuality
open InfoGeometry.Canonical.AmariBinarySimplexBridge
open InfoGeometry.Analysis.SpectralSurprisalLogDetBridge

/-- Barrier as trace of surprisal, on the concrete binary spectrum. -/
theorem barrier_trace_surprisal (p : ℝ) :
    intervalBarrier p = Matrix.trace (surprisalDiagonal ![p, 1 - p]) := by
  simp [intervalBarrier, leftSheetBarrier, rightSheetBarrier,
    InfoGeometry.Convex.SelfConcordantLogBarrier.logBarrier,
    surprisalDiagonal, spectralSurprisal, Matrix.trace_diagonal, Fin.sum_univ_two]
  ring

/-- Entropy is a weighted sum of those same surprisals. -/
theorem entropy_weighted_surprisal (p : ℝ) :
    -negativeEntropy p = p * spectralSurprisal ![p, 1 - p] 0 +
      (1 - p) * spectralSurprisal ![p, 1 - p] 1 := by
  simp [negativeEntropy, spectralSurprisal]
  ring

/-- Exact distinction between log-odds, barrier, and Fisher metric coefficients. -/
theorem barrier_hessian_decomposition {p : ℝ} (hp : p ∈ Set.Ioo (0 : ℝ) 1) :
    intervalBarrierHessian p =
      InfoGeometry.Probability.SimplexQuadraticResponse.logOddsMetric p - 2 * fisherMix p := by
  have hp0 := hp.1.ne'
  have hq0 := (sub_pos.mpr hp.2).ne'
  unfold intervalBarrierHessian InfoGeometry.Probability.SimplexQuadraticResponse.logOddsMetric fisherMix
  field_simp
  ring

/-- A genuine third derivative via the already proved barrier Hessian. -/
theorem hasDerivAt_barrierHessian {p : ℝ} (hp : p ∈ Set.Ioo (0 : ℝ) 1) :
    HasDerivAt intervalBarrierHessian (-2 / p ^ 3 + 2 / (1 - p) ^ 3) p := by
  have hp0 := hp.1.ne'
  have hq0 := (sub_pos.mpr hp.2).ne'
  have hleft := (hasDerivAt_const p (1 : ℝ)).div ((hasDerivAt_id p).pow 2) (pow_ne_zero _ hp0)
  have hright := (hasDerivAt_const p (1 : ℝ)).div
    (((hasDerivAt_const p (1 : ℝ)).sub (hasDerivAt_id p)).pow 2) (pow_ne_zero _ hq0)
  convert hleft.add hright using 1
  dsimp
  field_simp
  ring

/-- Actual Hessian derivative obeys the finite self-concordance inequality. -/
theorem barrier_self_concordance {p : ℝ} (hp : p ∈ Set.Ioo (0 : ℝ) 1) :
    |deriv intervalBarrierHessian p| ≤
      2 * Real.sqrt (intervalBarrierHessian p) * intervalBarrierHessian p := by
  let a : InfoGeometry.Modular.SelfConcordance.PositiveState (Fin 2) :=
    ⟨![p, 1 - p], by
      intro i
      fin_cases i
      · exact hp.1
      · exact sub_pos.mpr hp.2⟩
  have h := InfoGeometry.Modular.SelfConcordance.logBarrier_self_concordant a ![1, -1]
  have hH : InfoGeometry.Modular.SelfConcordance.hessLogBarrier a ![1, -1] =
      intervalBarrierHessian p := by
    simp [InfoGeometry.Modular.SelfConcordance.hessLogBarrier, a,
      intervalBarrierHessian, Fin.sum_univ_two, div_pow]
  have hT : InfoGeometry.Modular.SelfConcordance.thirdLogBarrier a ![1, -1] =
      -2 / p ^ 3 + 2 / (1 - p) ^ 3 := by
    simp [InfoGeometry.Modular.SelfConcordance.thirdLogBarrier, a,
      Fin.sum_univ_two, div_pow]
    ring
  rw [hH, hT] at h
  rw [(hasDerivAt_barrierHessian hp).deriv]
  exact h

/-- The convex conjugate of the positive-line negative-log barrier is attained
at the reciprocal dual coordinate. This is an actual maximum statement on the
native set of primal objective values, not a postulated primal/dual equality. -/
theorem negative_log_conjugate {y : ℝ} (hy : y < 0) :
    IsGreatest {z : ℝ | ∃ x : ℝ, 0 < x ∧ z = x * y + Real.log x}
      (-1 - Real.log (-y)) := by
  have hny : 0 < -y := neg_pos.mpr hy
  have hy0 : y ≠ 0 := ne_of_lt hy
  constructor
  · refine ⟨1 / (-y), one_div_pos.mpr hny, ?_⟩
    rw [Real.log_div one_ne_zero hny.ne', Real.log_one]
    field_simp
    ring
  · rintro z ⟨x, hx, rfl⟩
    have h := Real.log_le_sub_one_of_pos (mul_pos hx hny)
    rw [Real.log_mul hx.ne' hny.ne'] at h
    nlinarith

end InfoGeometry.Convex.BinaryBarrierSurprisal
