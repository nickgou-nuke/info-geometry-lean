import Mathlib.Tactic
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
open RealPin55ReflectionGenerators

@[simp]
theorem Q55_map (f : OQ55) (x : V55) :
    Q55 (f.1 x) = Q55 x := by
  exact f.2 x

theorem polar_map (f : OQ55) (u v : V55) :
    QuadraticMap.polar Q55 (f.1 u) (f.1 v) =
      QuadraticMap.polar Q55 u v := by
  unfold QuadraticMap.polar
  rw [← map_add, f.2 (u + v), f.2 u, f.2 v]

theorem Q55_sub_expansion (u v : V55) :
    Q55 (u - v) =
      Q55 u + Q55 v - QuadraticMap.polar Q55 u v := by
  rw [sub_eq_add_neg,
    QuadraticMap.map_add (Q55 : V55 → ℝ) u (-v),
    Q55.map_neg, QuadraticMap.polar_neg_right]
  ring

theorem Q55_parallelogram (u v : V55) :
    Q55 (u - v) + Q55 (u + v) =
      2 * Q55 u + 2 * Q55 v := by
  rw [Q55_sub_expansion,
    QuadraticMap.map_add (Q55 : V55 → ℝ) u v]
  ring

theorem Q_sub_add_Q_add (f : OQ55) (x : V55) :
    Q55 (f.1 x - x) + Q55 (f.1 x + x) = 4 * Q55 x := by
  rw [Q55_parallelogram, Q55_map]
  ring

theorem anisotropic_sub_or_add (f : OQ55) {x : V55} (hx : Q55 x ≠ 0) :
    Q55 (f.1 x - x) ≠ 0 \/ Q55 (f.1 x + x) ≠ 0 := by
  by_contra h
  push_neg at h
  have hsum := Q_sub_add_Q_add f x
  rw [h.1, h.2] at hsum
  exact hx (by linarith)

theorem anisotropicReflection_eq_self_of_polar_zero
    (a v : V55)
    (hav : QuadraticMap.polar Q55 a v = 0) :
    anisotropicReflection a v = v := by
  unfold anisotropicReflection
  rw [hav]
  simp

theorem anisotropicReflection_neg_self
    {x : V55}
    (hx : Q55 x ≠ 0) :
    anisotropicReflection x (-x) = x := by
  have h := anisotropicReflection_involutive hx x
  rw [anisotropicReflection_self hx] at h
  exact h

theorem reflection_self_maps_neg
    {x : V55}
    (hx : Q55 x ≠ 0) :
    anisotropicReflection x (-x) = x :=
  anisotropicReflection_neg_self hx

theorem polar_sub_image_eq_Q_sub
    (f : OQ55)
    (x : V55) :
    QuadraticMap.polar Q55 (f.1 x - x) (f.1 x) =
      Q55 (f.1 x - x) := by
  have hdiff :
      Q55 (f.1 x - x) =
        Q55 (f.1 x) + Q55 x -
          QuadraticMap.polar Q55 (f.1 x) x := by
    rw [sub_eq_add_neg,
      QuadraticMap.map_add (Q55 : V55 → ℝ) (f.1 x) (-x),
      Q55.map_neg, QuadraticMap.polar_neg_right]
    ring
  rw [QuadraticMap.polar_sub_left, polar_map,
    QuadraticMap.polar_self]
  rw [QuadraticMap.polar_comm (Q55 : V55 → ℝ) x (f.1 x), hdiff,
    f.2 x]
  simp only [two_nsmul]

theorem polar_add_image_eq_Q_add
    (f : OQ55)
    (x : V55) :
    QuadraticMap.polar Q55 (f.1 x + x) (f.1 x) =
      Q55 (f.1 x + x) := by
  rw [QuadraticMap.polar_add_left, polar_map,
    QuadraticMap.polar_self]
  rw [QuadraticMap.map_add (Q55 : V55 → ℝ) (f.1 x) x, f.2 x]
  rw [QuadraticMap.polar_comm (Q55 : V55 → ℝ) x (f.1 x)]
  simp only [two_nsmul]

theorem reflection_sub_maps_image (f : OQ55) {x : V55}
    (h : Q55 (f.1 x - x) ≠ 0) :
    anisotropicReflection (f.1 x - x) (f.1 x) = x := by
  unfold anisotropicReflection
  rw [polar_sub_image_eq_Q_sub f x, inv_mul_cancel₀ h, one_smul]
  abel

theorem reflection_add_maps_image (f : OQ55) {x : V55}
    (h : Q55 (f.1 x + x) ≠ 0) :
    anisotropicReflection (f.1 x + x) (f.1 x) = -x := by
  unfold anisotropicReflection
  rw [polar_add_image_eq_Q_add f x, inv_mul_cancel₀ h, one_smul]
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
    exact anisotropicReflection_neg_self hx

theorem exists_one_reflection_correction_of_sub
    (f : OQ55) {x : V55}
    (hsub : Q55 (f.1 x - x) ≠ 0) :
    ∃ a, Q55 a ≠ 0 ∧ anisotropicReflection a (f.1 x) = x :=
  ⟨f.1 x - x, hsub, reflection_sub_maps_image f hsub⟩

theorem exists_two_reflection_correction_of_add
    (f : OQ55) {x : V55}
    (hx : Q55 x ≠ 0)
    (hadd : Q55 (f.1 x + x) ≠ 0) :
    ∃ a b, Q55 a ≠ 0 ∧ Q55 b ≠ 0 ∧
      anisotropicReflection b (anisotropicReflection a (f.1 x)) = x := by
  refine ⟨f.1 x + x, x, hadd, hx, ?_⟩
  rw [reflection_add_maps_image f hadd]
  exact reflection_self_maps_neg hx

theorem canonical_reflection_correction
    (f : OQ55) {x : V55}
    (hx : Q55 x ≠ 0) :
    (Q55 (f.1 x - x) ≠ 0 ∧
      anisotropicReflection (f.1 x - x) (f.1 x) = x) ∨
    (Q55 (f.1 x + x) ≠ 0 ∧
      anisotropicReflection x
        (anisotropicReflection (f.1 x + x) (f.1 x)) = x) := by
  rcases anisotropic_sub_or_add f hx with hsub | hadd
  · exact Or.inl ⟨hsub, reflection_sub_maps_image f hsub⟩
  · exact Or.inr ⟨hadd, by
      rw [reflection_add_maps_image f hadd]
      exact reflection_self_maps_neg hx⟩

end RealO55CartanDieudonneStep
end noncomputable section
