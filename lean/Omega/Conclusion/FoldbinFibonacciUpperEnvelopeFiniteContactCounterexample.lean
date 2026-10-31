/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Omega.Conclusion.FoldbinFibonacciUpperEnvelopeFiniteContact

namespace Omega.Conclusion

/-- The upper-bound and auxiliary propositions in the paper-facing theorem do
not imply eventual strict separation: equal constant sequences satisfy the
upper bound and remain equal at every index. -/
theorem upper_bound_does_not_imply_finite_contact
    (same_exp_scale subexp_gap : Prop)
    (hsame : same_exp_scale) (hgap : subexp_gap) :
    ∃ dmax E : ℕ → ℕ,
      (∀ m, 1 ≤ m → dmax m ≤ E m) ∧
      same_exp_scale ∧ subexp_gap ∧
      ¬ ∃ M, ∀ m, M ≤ m → dmax m ≠ E m := by
  refine ⟨fun _ => 0, fun _ => 0, ?_, hsame, hgap, ?_⟩
  · intro m hm
    exact Nat.le_refl 0
  · rintro ⟨M, hstrict⟩
    have h := hstrict M le_rfl
    exact h rfl

end Omega.Conclusion
