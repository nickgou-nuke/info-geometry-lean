import Mathlib.Tactic

namespace Omega.Multiscale

/-- Shift invariance of normalized bulk and boundary integrals from their layer formulas. -/
theorem paper_app_solenoid_shift_invariance
    (bulkIntegral bulkShiftedIntegral boundaryIntegral boundaryShiftedIntegral : ℕ → ℝ)
    (bulkLayerFormula : ∀ n, bulkIntegral n = bulkShiftedIntegral n)
    (bulkNextLayerFormula : ∀ n, bulkShiftedIntegral n = bulkIntegral (n + 1))
    (boundaryLayerFormula : ∀ n, boundaryIntegral n = boundaryShiftedIntegral n)
    (boundaryNextLayerFormula : ∀ n, boundaryShiftedIntegral n = boundaryIntegral (n + 1)) :
    (∀ n, bulkIntegral n = bulkIntegral (n + 1)) ∧
      (∀ n, boundaryIntegral n = boundaryIntegral (n + 1)) := by
  have hBulk : ∀ n, bulkIntegral n = bulkIntegral (n + 1) := fun n =>
    (bulkLayerFormula n).trans (bulkNextLayerFormula n)
  have hBoundary : ∀ n, boundaryIntegral n = boundaryIntegral (n + 1) := fun n =>
    (boundaryLayerFormula n).trans (boundaryNextLayerFormula n)
  exact ⟨hBulk, hBoundary⟩

end Omega.Multiscale
