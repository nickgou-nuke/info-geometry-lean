/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Omega.Conclusion.CollisionGenfuncRadiusHalting

/-!
# Scope boundary for the collision generating-function radius statement

The source theorem assumes the two branch values of `R`; its coefficient
tail assumptions do not define or constrain `R`.  This file records the
exact piecewise equivalence and a countermodel showing that the coefficient
branch data alone do not imply the advertised radius.
-/

namespace Omega.Conclusion

theorem radius_piecewise_iff_branches (halts : Prop) [Decidable halts]
    (R rH rN : ℝ) :
    R = (if halts then rH else rN) ↔
      (halts → R = rH) ∧ (¬ halts → R = rN) := by
  constructor
  · intro h
    constructor
    · intro hh
      simpa [hh] using h
    · intro hnh
      simpa [hnh] using h
  · rintro ⟨hh, hnh⟩
    by_cases h : halts
    · simpa [h] using hh h
    · simpa [h] using hnh h

/-- Coefficient branch data by themselves do not force the claimed radius:
the nonhalting coefficients can all equal one while the independent value
`R` is chosen to be two.  The radius branch hypotheses in the source theorem
are therefore essential to its conclusion. -/
theorem collision_coefficients_do_not_determine_radius :
    ∃ (q T : ℕ) (halts : Bool) (a : ℕ → ℝ) (R : ℝ),
      2 ≤ q ∧
      (halts = false → ∀ t, a t = 1) ∧
      (halts = true → ∀ t, T ≤ t →
        a t = (2 : ℝ) ^ ((q - 1) * (t + 1))) ∧
      R ≠ if halts then 1 / (2 : ℝ) ^ (q - 1) else 1 := by
  refine ⟨2, 0, false, fun _ => 1, 2, by norm_num, ?_, ?_, ?_⟩
  · intro _ t
    rfl
  · intro h
    cases h
  · norm_num

end Omega.Conclusion
