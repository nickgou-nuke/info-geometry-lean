import InfoGeometry.Quantum.DikinApolloniusTrap
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Canonical

open InfoGeometry.Quantum.DikinApolloniusTrap Real

/-! Direct finite Dikin barrier and contraction packet. -/
theorem grand_canonical_dikin_apollonius_trap_synthesis
    (ξ r : ℝ) :
    (dikinScaleBarrier ξ = 2 * Real.log (Real.cosh ξ)) ∧
    (0 < dikinScaleMetric ξ) ∧
    (dikinScaleMetric 0 = 2) ∧
    (∀ y Ty Kc, 0 ≤ Kc → y ∈ dikinEquilibriumEllipsoid r → |Ty| ≤ Kc * |y| →
      2 * Ty ^ 2 ≤ (Kc * r) ^ 2) := by
  exact ⟨dikin_barrier_eq_two_log_cosh ξ,
    dikin_scale_metric_pos ξ,
    dikin_scale_metric_at_zero,
    fun y Ty Kc hKc hy hcontract =>
      blahut_arimoto_dikin_shrinkage Kc r y hKc hy Ty hcontract⟩

end InfoGeometry.Canonical
