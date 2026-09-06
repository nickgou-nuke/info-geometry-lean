import Experimental.Sandbox.Mobius.EvalCases

namespace Experimental.Sandbox.Mobius

lemma eval_none_ne_none_iff (M : InfoGeometry.MobiusTransform) :
    M.eval none ≠ none ↔ M.c ≠ 0 := by
  rw [ne_eq, ne_eq, not_iff_not]
  exact eval_none_eq_none_iff M

lemma eval_none_eq_some_iff (M : InfoGeometry.MobiusTransform) (w : ℂ) :
    M.eval none = some w ↔ M.c ≠ 0 ∧ w = M.a / M.c := by
  constructor
  · intro h
    have hc : M.c ≠ 0 := by
      rw [← eval_none_ne_none_iff M]
      rw [h]
      simp
    have hsome := eval_none_eq_some_of_c_ne_zero M hc
    injection h.symm.trans hsome with hw
    exact ⟨hc, hw⟩
  · intro h
    rw [h.2]
    exact eval_none_eq_some_of_c_ne_zero M h.1

lemma eval_none_some_value_unique
    (M : InfoGeometry.MobiusTransform) (w : ℂ) (h : M.eval none = some w) :
    w = M.a / M.c := by
  exact (eval_none_eq_some_iff M w).mp h |>.2

lemma c_ne_zero_of_eval_none_eq_some
    (M : InfoGeometry.MobiusTransform) (w : ℂ) (h : M.eval none = some w) :
    M.c ≠ 0 := by
  exact (eval_none_eq_some_iff M w).mp h |>.1

lemma eval_none_not_some_of_c_eq_zero
    (M : InfoGeometry.MobiusTransform) (w : ℂ) (hc : M.c = 0) :
    M.eval none ≠ some w := by
  intro h
  have hcne := c_ne_zero_of_eval_none_eq_some M w h
  exact hcne hc

end Experimental.Sandbox.Mobius
