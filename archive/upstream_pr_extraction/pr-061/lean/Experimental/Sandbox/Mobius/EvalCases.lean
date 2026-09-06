import InfoGeometry.Topology.MobiusGeometry

namespace Experimental.Sandbox.Mobius

lemma eval_some_eq_none_iff (M : InfoGeometry.MobiusTransform) (z : ℂ) :
    M.eval (some z) = none ↔ M.c * z + M.d = 0 := by
  by_cases h : M.c * z + M.d = 0
  · simp [InfoGeometry.MobiusTransform.eval, h]
  · simp [InfoGeometry.MobiusTransform.eval, h]

lemma eval_some_ne_none_iff (M : InfoGeometry.MobiusTransform) (z : ℂ) :
    M.eval (some z) ≠ none ↔ M.c * z + M.d ≠ 0 := by
  rw [ne_eq, ne_eq, not_iff_not]
  exact eval_some_eq_none_iff M z

lemma eval_some_eq_fractional_of_den_ne_zero
    (M : InfoGeometry.MobiusTransform) (z : ℂ) (hden : M.c * z + M.d ≠ 0) :
    M.eval (some z) = some ((M.a * z + M.b) / (M.c * z + M.d)) := by
  simp [InfoGeometry.MobiusTransform.eval, hden]

lemma eval_none_eq_none_iff (M : InfoGeometry.MobiusTransform) :
    M.eval none = none ↔ M.c = 0 := by
  by_cases h : M.c = 0
  · simp [InfoGeometry.MobiusTransform.eval, h]
  · simp [InfoGeometry.MobiusTransform.eval, h]

lemma eval_none_eq_some_of_c_ne_zero
    (M : InfoGeometry.MobiusTransform) (hc : M.c ≠ 0) :
    M.eval none = some (M.a / M.c) := by
  simp [InfoGeometry.MobiusTransform.eval, hc]

end Experimental.Sandbox.Mobius
