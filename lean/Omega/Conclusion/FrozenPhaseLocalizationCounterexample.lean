/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Omega.Conclusion.FrozenPhasePeakObstructionLocalization

namespace Omega.Conclusion

/-- The separation and frozen inequalities alone do not imply either the
collapse identity or the displayed beta identity. -/
theorem frozen_phase_inequalities_do_not_force_localization :
    ∃ gStar alphaStar alpha2 a aC betaInv : ℝ, ∃ hTheta : ℝ → ℝ,
      alpha2 < alphaStar ∧ aC < a ∧
      ¬ (∀ theta : ℝ, 1 ≤ theta → hTheta theta = gStar) ∧
      betaInv ≠ alphaStar / Real.log 2 := by
  refine ⟨0, 0, -1, 1, 0, 1, fun theta => if theta = 1 then 1 else 0,
    ?_, ?_, ?_, ?_⟩
  · norm_num
  · norm_num
  · intro hcollapse
    have h := hcollapse 1 (by norm_num)
    norm_num at h
  · simp

end Omega.Conclusion
