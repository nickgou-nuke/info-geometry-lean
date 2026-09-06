import InfoGeometry.ParaKahler.UnifiedPotential

namespace InfoGeometry.Canonical.UnifiedPotentialCapstone

open InfoGeometry.ParaKahler.UnifiedPotential

set_option linter.unusedVariables false

theorem verification_capstone (dξ dθ : ℝ) :
    (hessianMetricFromPotential 0 0 = 1 ∧
      hessianMetricFromPotential 1 1 = -1) ∧
      (berryFormFromPotential.det = 1) ∧
      ((maurerCartanForm dξ dθ).det = dξ ^ 2 - dθ ^ 2) ∧
      (dikinBarrierPotential 0 = 0) := by
  exact grand_master_potential_synthesis dξ dθ

end InfoGeometry.Canonical.UnifiedPotentialCapstone
