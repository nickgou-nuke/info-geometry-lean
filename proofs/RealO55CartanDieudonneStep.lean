import proofs.RealPin55ReflectionGenerators

/-! # The anisotropic-vector step in Cartan--Dieudonne for `Q55`

This owner isolates the local constructive step: an orthogonal map can be
corrected by one or two anisotropic reflections so that it fixes a prescribed
anisotropic vector. The induction on its orthogonal complement is separate.
-/

noncomputable section
namespace RealO55CartanDieudonneStep

open Clifford55
open RealPin55OrthogonalAction
open RealPin55QuadraticRepresentation

theorem polar_map (f : OQ55) (u v : V55) :
    QuadraticMap.polar Q55 (f.1 u) (f.1 v) =
      QuadraticMap.polar Q55 u v := by
  unfold QuadraticMap.polar
  rw [← map_add, f.2 (u + v), f.2 u, f.2 v]

theorem Q_sub_add_Q_add (f : OQ55) (x : V55) :
    Q55 (f.1 x - x) + Q55 (f.1 x + x) = 4 * Q55 x := by
  rw [sub_eq_add_neg,
    QuadraticMap.map_add (Q55 : V55 → ℝ) (f.1 x) (-x),
    QuadraticMap.map_add (Q55 : V55 → ℝ) (f.1 x) x,
    Q55.map_neg, QuadraticMap.polar_neg_right]
  rw [f.2 x]
  ring

theorem anisotropic_sub_or_add (f : OQ55) {x : V55} (hx : Q55 x ≠ 0) :
    Q55 (f.1 x - x) ≠ 0 \/ Q55 (f.1 x + x) ≠ 0 := by
  by_contra h
  push_neg at h
  have hsum := Q_sub_add_Q_add f x
  rw [h.1, h.2] at hsum
  exact hx (by linarith)

theorem reflection_sub_maps_image (f : OQ55) {x : V55}
    (h : Q55 (f.1 x - x) ≠ 0) :
    anisotropicReflection (f.1 x - x) (f.1 x) = x := by
  unfold anisotropicReflection
  have hpolar :
      QuadraticMap.polar Q55 (f.1 x - x) (f.1 x) =
        Q55 (f.1 x - x) := by
    have hdiff :
        Q55 (f.1 x - x) =
          Q55 (f.1 x) + Q55 x - QuadraticMap.polar Q55 (f.1 x) x := by
      rw [sub_eq_add_neg,
        QuadraticMap.map_add (Q55 : V55 → ℝ) (f.1 x) (-x),
        Q55.map_neg, QuadraticMap.polar_neg_right]
      ring
    rw [QuadraticMap.polar_sub_left, polar_map,
      QuadraticMap.polar_self]
    unfold QuadraticMap.polar
    rw [add_comm x (f.1 x)]
    rw [hdiff,
      QuadraticMap.map_add (Q55 : V55 → ℝ) (f.1 x) x,
      f.2 x]
    ring
  rw [hpolar, inv_mul_cancel₀ h, one_smul]
  abel

theorem reflection_add_maps_image (f : OQ55) {x : V55}
    (h : Q55 (f.1 x + x) ≠ 0) :
    anisotropicReflection (f.1 x + x) (f.1 x) = -x := by
  unfold anisotropicReflection
  have hpolar :
      QuadraticMap.polar Q55 (f.1 x + x) (f.1 x) =
        Q55 (f.1 x + x) := by
    rw [QuadraticMap.polar_add_left, polar_map,
      QuadraticMap.polar_self]
    unfold QuadraticMap.polar
    rw [add_comm x (f.1 x)]
    rw [QuadraticMap.map_add (Q55 : V55 → ℝ) (f.1 x) x,
      f.2 x]
    ring
  rw [hpolar, inv_mul_cancel₀ h, one_smul]
  abel

/-- One or two anisotropic reflections send `f x` back to `x`. -/
theorem exists_reflection_correction (f : OQ55) {x : V55} (hx : Q55 x ≠ 0) :
    (exists a, Q55 a ≠ 0 /\ anisotropicReflection a (f.1 x) = x) \/
    (exists a b, Q55 a ≠ 0 /\ Q55 b ≠ 0 /\
      anisotropicReflection b (anisotropicReflection a (f.1 x)) = x) := by
  rcases anisotropic_sub_or_add f hx with hsub | hadd
  · exact Or.inl <| ⟨f.1 x - x, hsub, reflection_sub_maps_image f hsub⟩
  · refine Or.inr <| ⟨f.1 x + x, x, hadd, hx, ?_⟩
    rw [reflection_add_maps_image f hadd]
    have hc : (Q55 x)⁻¹ * (2 * Q55 x) = 2 := by
      field_simp
    have hcneg : (Q55 x)⁻¹ * -(2 * Q55 x) = -2 := by
      rw [mul_neg, hc]
    simp only [anisotropicReflection, QuadraticMap.polar_neg_right,
      QuadraticMap.polar_self]
    have htwo : (2 : ℕ) • Q55 x = 2 * Q55 x := by norm_num
    rw [htwo]
    rw [hcneg]
    module

end RealO55CartanDieudonneStep
end noncomputable section
