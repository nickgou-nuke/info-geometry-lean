import InfoGeometry.Core.ProjectiveSimplex
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.Convex.Extreme

open Set

theorem uniqueMaximum_is_extremePoint {ι : Type*} [Fintype ι] [Nonempty ι]
  (f : (ι → ℝ) → ℝ) (x : ι → ℝ)
  (h_conv : ConvexOn ℝ (stdSimplex ℝ ι) f)
  (hx : x ∈ stdSimplex ℝ ι)
  (h_max : ∀ y ∈ stdSimplex ℝ ι, y ≠ x → f y < f x) :
  x ∈ extremePoints ℝ (stdSimplex ℝ ι) := by
  rw [mem_extremePoints_iff_forall_segment]
  refine ⟨hx, fun y hy z hz hseg => ?_⟩
  by_contra h
  push_neg at h
  have hy_ne : y ≠ x := h.1
  have hz_ne : z ≠ x := h.2
  have hy_lt : f y < f x := h_max y hy hy_ne
  have hz_lt : f z < f x := h_max z hz hz_ne
  rcases hseg with ⟨a, b, ha, hb, hab, hEq⟩
  have h_conv2 := h_conv.2 hy hz ha hb hab
  have ha_pos : 0 < a := lt_of_le_of_ne ha (fun ha0 => by
    subst ha0
    rw [zero_add] at hab
    subst hab
    simp only [zero_smul, one_smul, zero_add] at hEq
    exact hz_ne hEq
  )
  have hb_pos : 0 < b := lt_of_le_of_ne hb (fun hb0 => by
    subst hb0
    rw [add_zero] at hab
    subst hab
    simp only [zero_smul, one_smul, add_zero] at hEq
    exact hy_ne hEq
  )
  have h_lt1 : a * f y < a * f x := mul_lt_mul_of_pos_left hy_lt ha_pos
  have h_lt2 : b * f z < b * f x := mul_lt_mul_of_pos_left hz_lt hb_pos
  have h_lt : a * f y + b * f z < a * f x + b * f x := add_lt_add h_lt1 h_lt2
  rw [← add_mul, hab, one_mul] at h_lt
  rw [hEq] at h_conv2
  exact lt_irrefl _ (h_conv2.trans_lt h_lt)
