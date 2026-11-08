import Experimental.Sandbox.Mobius.FiniteImageFacts

namespace Experimental.Sandbox.Mobius

lemma comp_num_apply
    (M1 M2 : InfoGeometry.MobiusTransform) (z : ℂ) :
    (InfoGeometry.comp M1 M2).a * z + (InfoGeometry.comp M1 M2).b =
      M1.a * (M2.a * z + M2.b) + M1.b * (M2.c * z + M2.d) := by
  simp [InfoGeometry.comp]
  ring

lemma comp_den_apply
    (M1 M2 : InfoGeometry.MobiusTransform) (z : ℂ) :
    (InfoGeometry.comp M1 M2).c * z + (InfoGeometry.comp M1 M2).d =
      M1.c * (M2.a * z + M2.b) + M1.d * (M2.c * z + M2.d) := by
  simp [InfoGeometry.comp]
  ring

lemma comp_num_apply_as_nested_num
    (M1 M2 : InfoGeometry.MobiusTransform) (z : ℂ)
    (h2 : M2.c * z + M2.d ≠ 0) :
    (InfoGeometry.comp M1 M2).a * z + (InfoGeometry.comp M1 M2).b =
      (M1.a * ((M2.a * z + M2.b) / (M2.c * z + M2.d)) + M1.b) *
        (M2.c * z + M2.d) := by
  have h2' : z * M2.c + M2.d ≠ 0 := by simpa [mul_comm] using h2
  rw [comp_num_apply]
  field_simp [h2, h2']

lemma comp_den_apply_as_nested_den
    (M1 M2 : InfoGeometry.MobiusTransform) (z : ℂ)
    (h2 : M2.c * z + M2.d ≠ 0) :
    (InfoGeometry.comp M1 M2).c * z + (InfoGeometry.comp M1 M2).d =
      (M1.c * ((M2.a * z + M2.b) / (M2.c * z + M2.d)) + M1.d) *
        (M2.c * z + M2.d) := by
  have h2' : z * M2.c + M2.d ≠ 0 := by simpa [mul_comm] using h2
  rw [comp_den_apply]
  field_simp [h2, h2']

lemma comp_den_ne_zero_of_nested_den_ne_zero
    (M1 M2 : InfoGeometry.MobiusTransform) (z : ℂ)
    (h2 : M2.c * z + M2.d ≠ 0)
    (h1 : M1.c * ((M2.a * z + M2.b) / (M2.c * z + M2.d)) + M1.d ≠ 0) :
    (InfoGeometry.comp M1 M2).c * z + (InfoGeometry.comp M1 M2).d ≠ 0 := by
  rw [comp_den_apply_as_nested_den M1 M2 z h2]
  exact mul_ne_zero h1 h2

lemma comp_fractional_apply_eq_nested
    (M1 M2 : InfoGeometry.MobiusTransform) (z : ℂ)
    (h2 : M2.c * z + M2.d ≠ 0) :
    ((InfoGeometry.comp M1 M2).a * z + (InfoGeometry.comp M1 M2).b) /
        ((InfoGeometry.comp M1 M2).c * z + (InfoGeometry.comp M1 M2).d) =
      (M1.a * ((M2.a * z + M2.b) / (M2.c * z + M2.d)) + M1.b) /
        (M1.c * ((M2.a * z + M2.b) / (M2.c * z + M2.d)) + M1.d) := by
  rw [comp_num_apply_as_nested_num M1 M2 z h2, comp_den_apply_as_nested_den M1 M2 z h2]
  rw [mul_div_mul_right _ _ h2]

lemma comp_eval_some_eq_some_of_nested_den_ne_zero
    (M1 M2 : InfoGeometry.MobiusTransform) (z : ℂ)
    (h2 : M2.c * z + M2.d ≠ 0)
    (h1 : M1.c * ((M2.a * z + M2.b) / (M2.c * z + M2.d)) + M1.d ≠ 0) :
    (InfoGeometry.comp M1 M2).eval (some z) =
      some ((M1.a * ((M2.a * z + M2.b) / (M2.c * z + M2.d)) + M1.b) /
        (M1.c * ((M2.a * z + M2.b) / (M2.c * z + M2.d)) + M1.d)) := by
  have hc := comp_den_ne_zero_of_nested_den_ne_zero M1 M2 z h2 h1
  rw [eval_some_eq_fractional_of_den_ne_zero (InfoGeometry.comp M1 M2) z hc]
  congr 1
  exact comp_fractional_apply_eq_nested M1 M2 z h2

end Experimental.Sandbox.Mobius
