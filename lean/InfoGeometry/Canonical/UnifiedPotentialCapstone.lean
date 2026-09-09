import InfoGeometry.ParaKahler.UnifiedPotential

namespace InfoGeometry.Canonical.UnifiedPotentialCapstone

open InfoGeometry.ParaKahler.UnifiedPotential

theorem verification_capstone (dξ dθ : ℝ) :
    (hessianMetricFromPotential 0 0 = 1 ∧
      hessianMetricFromPotential 1 1 = -1) ∧
      (berryFormFromPotential.det = 1) ∧
      ((maurerCartanForm dξ dθ).det = dξ ^ 2 - dθ ^ 2) ∧
      (dikinBarrierPotential 0 = 0) := by
  exact ⟨⟨(hessian_matches_parametric).1,
      (hessian_matches_parametric).2.1⟩,
    (berry_form_properties).1,
    (maurer_cartan_trace_and_det dξ dθ).2,
    (dikin_barrier_at_zero).1⟩

end InfoGeometry.Canonical.UnifiedPotentialCapstone
