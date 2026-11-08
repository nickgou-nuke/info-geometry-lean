import Experimental.Sandbox.Mobius.FiniteImageFacts

namespace Experimental.Sandbox.Mobius

lemma inv_num_apply
    (M : InfoGeometry.MobiusTransform) (z : ℂ) :
    (InfoGeometry.inv M).a * z + (InfoGeometry.inv M).b = M.d * z - M.b := by
  simp [InfoGeometry.inv]
  ring

lemma inv_den_apply
    (M : InfoGeometry.MobiusTransform) (z : ℂ) :
    (InfoGeometry.inv M).c * z + (InfoGeometry.inv M).d = -M.c * z + M.a := by
  simp [InfoGeometry.inv]

lemma inv_eval_some_eq_fractional_of_den_ne_zero
    (M : InfoGeometry.MobiusTransform) (z : ℂ)
    (hden : -M.c * z + M.a ≠ 0) :
    (InfoGeometry.inv M).eval (some z) = some ((M.d * z - M.b) / (-M.c * z + M.a)) := by
  have hden' : (InfoGeometry.inv M).c * z + (InfoGeometry.inv M).d ≠ 0 := by
    simpa [inv_den_apply] using hden
  rw [eval_some_eq_fractional_of_den_ne_zero (InfoGeometry.inv M) z hden']
  simp [inv_num_apply, inv_den_apply]

lemma inv_den_at_image_ne_zero
    (M : InfoGeometry.MobiusTransform) (z : ℂ)
    (hden : M.c * z + M.d ≠ 0) :
    -M.c * ((M.a * z + M.b) / (M.c * z + M.d)) + M.a ≠ 0 := by
  intro hzero
  have hden' : z * M.c + M.d ≠ 0 := by simpa [mul_comm] using hden
  have hmul : M.a * M.d - M.b * M.c = 0 := by
    field_simp [hden, hden'] at hzero
    ring_nf at hzero ⊢
    exact hzero
  exact M.det_ne_zero hmul

lemma inv_eval_after_eval_some_eq
    (M : InfoGeometry.MobiusTransform) (z w : ℂ)
    (h : M.eval (some z) = some w) :
    (InfoGeometry.inv M).eval (some w) = some z := by
  have hleft := InfoGeometry.eval_inv_left M (some z)
  rw [h] at hleft
  exact hleft

lemma eval_after_inv_eval_some_eq
    (M : InfoGeometry.MobiusTransform) (z w : ℂ)
    (h : (InfoGeometry.inv M).eval (some z) = some w) :
    M.eval (some w) = some z := by
  have hright := InfoGeometry.eval_inv M (some z)
  rw [h] at hright
  exact hright

end Experimental.Sandbox.Mobius
