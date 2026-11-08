/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Omega.Conclusion.SelfdualScaleMellinDoesNotForceVerticalPeriodicity

namespace Omega.Conclusion

/-- Functional symmetry and real values on the critical line do not imply
vertical nonperiodicity: the zero function satisfies both and has every
vertical period. -/
theorem selfdual_real_critical_line_can_be_periodic :
    ∃ X : ℂ → ℂ,
      (∀ s : ℂ, X s = X (1 - s)) ∧
      (∀ t : ℝ, ∃ r : ℝ,
        X (((1 : ℂ) / 2) + t * Complex.I) = r) ∧
      ∃ T : ℝ, T ≠ 0 ∧
        ∀ s : ℂ, X (s + T * Complex.I) = X s := by
  refine ⟨fun _ => 0, ?_, ?_, ⟨1, by norm_num, ?_⟩⟩
  · intro s
    rfl
  · intro t
    exact ⟨0, by simp⟩
  · intro s
    rfl

end Omega.Conclusion
