import Mathlib.Tactic
import Mathlib.Analysis.SpecificLimits.Normed

namespace Omega.Multiscale

open Filter Topology

/-- Concrete normalized bulk, boundary, defect, limit, and budget data. -/
structure RobustNormalizedStokesWithDefectBudgetData where
  normalizedBulk : ℕ → ℝ
  normalizedBoundary : ℕ → ℝ
  normalizedDefect : ℕ → ℝ
  bulkLimit : ℝ
  boundaryLimit : ℝ
  defectLimit : ℝ
  defectBudget : ℝ

/-- Layerwise normalized Stokes identities pass to the limit and preserve the defect budget. -/
theorem paper_app_robust_normalized_stokes_with_defect_budget
    (D : RobustNormalizedStokesWithDefectBudgetData)
    (layerwiseStokes :
      ∀ n, D.normalizedBulk n - D.normalizedBoundary n = D.normalizedDefect n)
    (bulk_tendsto : Tendsto D.normalizedBulk atTop (𝓝 D.bulkLimit))
    (boundary_tendsto : Tendsto D.normalizedBoundary atTop (𝓝 D.boundaryLimit))
    (defect_tendsto : Tendsto D.normalizedDefect atTop (𝓝 D.defectLimit))
    (defectLimit_abs_le_budget : |D.defectLimit| ≤ D.defectBudget) :
    D.bulkLimit - D.boundaryLimit = D.defectLimit ∧
      |D.bulkLimit - D.boundaryLimit| ≤ D.defectBudget := by
  have hSub :
      Tendsto (fun n => D.normalizedBulk n - D.normalizedBoundary n) atTop
        (𝓝 (D.bulkLimit - D.boundaryLimit)) :=
    bulk_tendsto.sub boundary_tendsto
  have hDefect :
      Tendsto (fun n => D.normalizedBulk n - D.normalizedBoundary n) atTop (𝓝 D.defectLimit) := by
    simpa [funext layerwiseStokes] using defect_tendsto
  have hId : D.bulkLimit - D.boundaryLimit = D.defectLimit :=
    tendsto_nhds_unique hSub hDefect
  exact ⟨hId, by simpa [hId] using defectLimit_abs_le_budget⟩

end Omega.Multiscale
