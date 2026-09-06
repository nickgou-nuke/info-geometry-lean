import Mathlib
import InfoGeometry.Routing.FiniteSoftmax

/-! Finite algebraic symmetry of routing weights.

This owner proves finite reindexing invariance and the corresponding uniform
usage consequence for a left-invariant score.  It does not introduce a
measure-theoretic data action or a general balanced-usage theorem.
-/

namespace InfoGeometry.Routing.FiniteRoutingSymmetry

open scoped BigOperators

theorem softmax_weight_left_invariant {G : Type*} [Group G] [Fintype G]
    (score : G → ℝ) (tau : ℝ) (h_score : ∀ h g, score (h * g) = score g)
    (h g : G) :
    FiniteSoftmax.weight score tau (h * g) =
      FiniteSoftmax.weight score tau g := by
  unfold FiniteSoftmax.weight
  rw [h_score]

def leftTranslate {G : Type*} [Group G] (h : G) : G ≃ G where
  toFun g := h * g
  invFun g := h⁻¹ * g
  left_inv g := by simp
  right_inv g := by simp

def rightTranslate {G : Type*} [Group G] (h : G) : G ≃ G where
  toFun g := g * h
  invFun g := g * h⁻¹
  left_inv g := by simp [mul_assoc]
  right_inv g := by simp [mul_assoc]

theorem sum_right_translate {G : Type*} [Group G] [Fintype G]
    (w : G → ℝ) (h : G) :
    (∑ g, w (g * h)) = ∑ g, w g := by
  have hs := Equiv.sum_comp (rightTranslate h) w
  change (∑ g, w (g * h)) = ∑ g, w g at hs
  exact hs

theorem sum_left_translate {G : Type*} [Group G] [Fintype G]
    (w : G → ℝ) (h : G) :
    (∑ g, w (h * g)) = ∑ g, w g := by
  have hs := Equiv.sum_comp (leftTranslate h) w
  change (∑ g, w (h * g)) = ∑ g, w g at hs
  exact hs

theorem sum_left_translate_normalized {G : Type*} [Group G] [Fintype G]
    (w : G → ℝ) (h : G) (c : ℝ) :
    (∑ g, c * w (h * g)) = ∑ g, c * w g := by
  rw [← Finset.mul_sum, ← Finset.mul_sum, sum_left_translate]

noncomputable def uniformAverage {G : Type*} [Fintype G] (w : G → ℝ) : ℝ :=
  (Fintype.card G : ℝ)⁻¹ * ∑ g, w g

theorem uniformAverage_left_translate {G : Type*} [Group G] [Fintype G]
    (w : G → ℝ) (h : G) :
    uniformAverage (fun g => w (h * g)) = uniformAverage w := by
  unfold uniformAverage
  change (Fintype.card G : ℝ)⁻¹ * (∑ g, w (h * g)) = _
  rw [sum_left_translate]

theorem left_invariant_weights_uniform {G : Type*} [Group G] [Fintype G]
    (w : G → ℝ) (h_invariant : ∀ h g, w (h * g) = w g)
    (h_sum : ∑ g, w g = 1) (g : G) :
    w g = (Fintype.card G : ℝ)⁻¹ := by
  have hw : w g = w 1 := by
    have h := h_invariant g⁻¹ g
    simpa using h.symm
  have hconst : (∑ x, w x) = (Fintype.card G : ℝ) * w 1 := by
    calc
      (∑ x, w x) = ∑ x, w 1 := by
        apply Finset.sum_congr rfl
        intro x hx
        have h := h_invariant x⁻¹ x
        simpa using h.symm
      _ = (Fintype.card G : ℝ) * w 1 := by simp [nsmul_eq_mul]
  have hcard : (Fintype.card G : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  rw [hw]
  rw [hconst] at h_sum
  field_simp [hcard]
  simpa [mul_comm] using h_sum

theorem softmax_weight_uniform_of_left_invariant_score
    {G : Type*} [Group G] [Fintype G] [Nonempty G]
    (score : G → ℝ) (tau : ℝ)
    (h_score : ∀ h g, score (h * g) = score g) (g : G) :
    FiniteSoftmax.weight score tau g = (Fintype.card G : ℝ)⁻¹ := by
  apply left_invariant_weights_uniform
    (w := FiniteSoftmax.weight score tau)
  · exact fun h g => softmax_weight_left_invariant score tau h_score h g
  · exact FiniteSoftmax.weight_sum_one score tau

theorem orbit_average_softmax_weight_uniform
    {G : Type*} [Group G] [Fintype G] [Nonempty G]
    (score : G → ℝ) (tau : ℝ) (g : G) :
    (Fintype.card G : ℝ)⁻¹ *
        (∑ h, FiniteSoftmax.weight score tau (h * g)) =
      (Fintype.card G : ℝ)⁻¹ := by
  rw [sum_right_translate]
  rw [FiniteSoftmax.weight_sum_one score tau]
  simp

end InfoGeometry.Routing.FiniteRoutingSymmetry
