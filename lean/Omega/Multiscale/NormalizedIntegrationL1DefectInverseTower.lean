import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic

namespace Omega.Multiscale

open Filter Topology

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

/-- The limiting Stokes identity for a normalized inverse tower with `ℓ¹` tail control. -/
theorem paper_app_normalized_integration_l1_defect_inverse_tower
    (normalizedBulk normalizedBoundary normalizedDefect : ℕ → ℝ)
    (bulkLimit boundaryLimit defectLimit : ℝ)
    (bulkTailBound boundaryTailBound defectTailBound : ℕ → ℝ)
    (layerwiseStokes :
      ∀ n, normalizedBulk n - normalizedBoundary n = normalizedDefect n)
    (bulk_tail : ∀ n, |bulkLimit - normalizedBulk n| ≤ bulkTailBound n)
    (boundary_tail : ∀ n, |boundaryLimit - normalizedBoundary n| ≤ boundaryTailBound n)
    (defect_tail : ∀ n, |defectLimit - normalizedDefect n| ≤ defectTailBound n)
    (bulkTail_tendsto_zero : Tendsto bulkTailBound atTop (𝓝 0))
    (boundaryTail_tendsto_zero : Tendsto boundaryTailBound atTop (𝓝 0))
    (defectTail_tendsto_zero : Tendsto defectTailBound atTop (𝓝 0)) :
    Tendsto normalizedBulk atTop (𝓝 bulkLimit) ∧
      (∀ N, |bulkLimit - normalizedBulk N| ≤ bulkTailBound N) ∧
      Tendsto normalizedBoundary atTop (𝓝 boundaryLimit) ∧
        bulkLimit - boundaryLimit = defectLimit := by
  have hBulk : Tendsto normalizedBulk atTop (𝓝 bulkLimit) :=
    tendsto_of_abs_sub_le bulk_tail bulkTail_tendsto_zero
  have hBoundary : Tendsto normalizedBoundary atTop (𝓝 boundaryLimit) :=
    tendsto_of_abs_sub_le boundary_tail boundaryTail_tendsto_zero
  have hDefect : Tendsto normalizedDefect atTop (𝓝 defectLimit) :=
    tendsto_of_abs_sub_le defect_tail defectTail_tendsto_zero
  have hSub :
      Tendsto (fun n => normalizedBulk n - normalizedBoundary n) atTop
        (𝓝 (bulkLimit - boundaryLimit)) :=
    hBulk.sub hBoundary
  have hDefectEq :
      Tendsto (fun n => normalizedBulk n - normalizedBoundary n) atTop (𝓝 defectLimit) := by
    simpa [funext layerwiseStokes] using hDefect
  have hLimitStokes : bulkLimit - boundaryLimit = defectLimit :=
    tendsto_nhds_unique hSub hDefectEq
  exact ⟨hBulk, bulk_tail, hBoundary, hLimitStokes⟩

end Omega.Multiscale
