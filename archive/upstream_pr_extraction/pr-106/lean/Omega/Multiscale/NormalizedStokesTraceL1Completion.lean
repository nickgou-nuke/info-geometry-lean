import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic
import Omega.Multiscale.NormalizedIntegrationL1DefectInverseTower

namespace Omega.Multiscale

open Filter Topology

/-- Concrete sequences, limits, tail budgets, and trace functional for normalized Stokes
completion. The compatibility and trace laws are supplied to the owner theorem explicitly. -/
structure NormalizedStokesTraceL1CompletionData where
  normalizedBulk : ℕ → ℝ
  normalizedBoundary : ℕ → ℝ
  normalizedDefect : ℕ → ℝ
  bulkLimit : ℝ
  boundaryLimit : ℝ
  defectLimit : ℝ
  bulkTailBound : ℕ → ℝ
  boundaryTailBound : ℕ → ℝ
  defectTailBound : ℕ → ℝ
  stableIndex : ℕ
  stableValue : ℝ
  extensionValue : ℝ
  traceFunctional : (ℕ → ℝ) → ℝ

private theorem tendsto_of_abs_sub_le
    {u : ℕ → ℝ} {L : ℝ} {b : ℕ → ℝ}
    (hBound : ∀ n, |L - u n| ≤ b n)
    (hTail : Tendsto b atTop (𝓝 0)) :
    Tendsto u atTop (𝓝 L) := by
  have hNorm :
      Tendsto (fun n => ‖u n - L‖) atTop (𝓝 0) := by
    have hAbs :
        Tendsto (fun n => |L - u n|) atTop (𝓝 0) :=
      squeeze_zero' (Eventually.of_forall fun _ => abs_nonneg _) (Eventually.of_forall hBound)
        hTail
    simpa [Real.norm_eq_abs, abs_sub_comm] using hAbs
  exact tendsto_iff_norm_sub_tendsto_zero.2 hNorm

/-- A tail-invariant trace completion yields the limiting Stokes law and agrees with the stable
boundary value. -/
theorem paper_app_normalized_stokes_trace_l1_completion
    (D : NormalizedStokesTraceL1CompletionData)
    (layerwiseStokes :
      ∀ n, D.normalizedBulk n - D.normalizedBoundary n = D.normalizedDefect n)
    (bulk_tail : ∀ n, |D.bulkLimit - D.normalizedBulk n| ≤ D.bulkTailBound n)
    (boundary_tail : ∀ n, |D.boundaryLimit - D.normalizedBoundary n| ≤ D.boundaryTailBound n)
    (defect_tail : ∀ n, |D.defectLimit - D.normalizedDefect n| ≤ D.defectTailBound n)
    (bulkTail_tendsto_zero : Tendsto D.bulkTailBound atTop (𝓝 0))
    (boundaryTail_tendsto_zero : Tendsto D.boundaryTailBound atTop (𝓝 0))
    (defectTail_tendsto_zero : Tendsto D.defectTailBound atTop (𝓝 0))
    (boundary_eventually_stable :
      ∀ n, D.stableIndex ≤ n → D.normalizedBoundary n = D.stableValue)
    (trace_respects_tail :
      ∀ u v : ℕ → ℝ, (∃ N, ∀ n, N ≤ n → u n = v n) → D.traceFunctional u = D.traceFunctional v)
    (trace_on_constant : ∀ c : ℝ, D.traceFunctional (fun _ => c) = c)
    (trace_on_boundary : D.traceFunctional D.normalizedBoundary = D.extensionValue) :
    D.boundaryLimit = D.stableValue ∧
      D.bulkLimit - D.boundaryLimit = D.defectLimit ∧
        D.extensionValue = D.boundaryLimit := by
  rcases paper_app_normalized_integration_l1_defect_inverse_tower
      D.normalizedBulk D.normalizedBoundary D.normalizedDefect D.bulkLimit D.boundaryLimit
      D.defectLimit D.bulkTailBound D.boundaryTailBound D.defectTailBound layerwiseStokes
      bulk_tail boundary_tail defect_tail bulkTail_tendsto_zero boundaryTail_tendsto_zero
      defectTail_tendsto_zero with
    ⟨_, _, hBoundary, hLimitStokes⟩
  have hStable : Tendsto D.normalizedBoundary atTop (𝓝 D.stableValue) :=
    tendsto_atTop_of_eventually_const boundary_eventually_stable
  have hAgree : D.boundaryLimit = D.stableValue :=
    tendsto_nhds_unique hBoundary hStable
  have hExtensionStable : D.extensionValue = D.stableValue := by
    have hTailEq :
        D.traceFunctional D.normalizedBoundary = D.traceFunctional (fun _ => D.stableValue) := by
      refine trace_respects_tail D.normalizedBoundary (fun _ => D.stableValue) ?_
      exact ⟨D.stableIndex, fun n hn => boundary_eventually_stable n hn⟩
    calc
      D.extensionValue = D.traceFunctional D.normalizedBoundary := by
        symm
        exact trace_on_boundary
      _ = D.traceFunctional (fun _ => D.stableValue) := hTailEq
      _ = D.stableValue := trace_on_constant D.stableValue
  exact ⟨hAgree, hLimitStokes, hExtensionStable.trans hAgree.symm⟩

end Omega.Multiscale
