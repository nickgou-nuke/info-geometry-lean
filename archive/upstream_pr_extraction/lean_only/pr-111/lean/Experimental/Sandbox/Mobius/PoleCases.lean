import Experimental.Sandbox.Mobius.EvalCases

namespace Experimental.Sandbox.Mobius

lemma denom_eq_zero_iff_eq_pole_of_c_ne_zero
    (M : InfoGeometry.MobiusTransform) (z : ℂ) (hc : M.c ≠ 0) :
    M.c * z + M.d = 0 ↔ z = -M.d / M.c := by
  constructor
  · intro h
    have hz : M.c * z = -M.d := by
      exact eq_neg_of_add_eq_zero_left h
    calc
      z = (M.c * z) / M.c := by field_simp [hc]
      _ = (-M.d) / M.c := by rw [hz]
      _ = -M.d / M.c := rfl
  · intro h
    rw [h]
    field_simp [hc]
    ring

lemma pole_maps_to_none_of_c_ne_zero
    (M : InfoGeometry.MobiusTransform) (hc : M.c ≠ 0) :
    M.eval (some (-M.d / M.c)) = none := by
  exact (eval_some_eq_none_iff M (-M.d / M.c)).mpr
    ((denom_eq_zero_iff_eq_pole_of_c_ne_zero M (-M.d / M.c) hc).mpr rfl)

lemma eval_some_eq_none_iff_eq_pole_of_c_ne_zero
    (M : InfoGeometry.MobiusTransform) (z : ℂ) (hc : M.c ≠ 0) :
    M.eval (some z) = none ↔ z = -M.d / M.c := by
  rw [eval_some_eq_none_iff]
  exact denom_eq_zero_iff_eq_pole_of_c_ne_zero M z hc

lemma finite_ne_pole_of_eval_some
    (M : InfoGeometry.MobiusTransform) (z w : ℂ) (hc : M.c ≠ 0)
    (h : M.eval (some z) = some w) :
    z ≠ -M.d / M.c := by
  intro hz
  have hnone : M.eval (some z) = none :=
    (eval_some_eq_none_iff_eq_pole_of_c_ne_zero M z hc).mpr hz
  rw [h] at hnone
  cases hnone

end Experimental.Sandbox.Mobius
