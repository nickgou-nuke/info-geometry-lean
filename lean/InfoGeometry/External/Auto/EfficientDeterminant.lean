import Mathlib.Tactic.Ring
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Tactic.Linarith
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic

theorem orientation_matrix_det {R : Type*} [CommRing R] (xA yA xB yB xC yC : R) :
  (xA * yB * 1 + yA * 1 * xC + 1 * xB * yC) - (1 * yB * xC + xA * 1 * yC + yA * xB * 1) =
  (xB - xA) * (yC - yA) - (xC - xA) * (yB - yA) := by
  ring

def IsMinimumVert (S : Set ℝ) (m : ℝ) : Prop :=
  m ∈ S ∧ ∀ x ∈ S, m ≤ x

def IsConvexHullVertex (S : Set ℝ) (v : ℝ) : Prop :=
  v ∈ S ∧ ∀ x y, x ∈ S → y ∈ S → ∀ t : ℝ, 0 < t → t < 1 → v = t * x + (1 - t) * y → v = x ∨ v = y

theorem min_is_convex_hull_vertex (S : Set ℝ) (m : ℝ) (h : IsMinimumVert S m) :
  IsConvexHullVertex S m := by
  refine ⟨h.1, fun x y hx hy t ht1 ht2 heq => ?_⟩
  have hmx : m ≤ x := h.2 x hx
  have hmy : m ≤ y := h.2 y hy
  have H1 : 0 ≤ t * (x - m) := mul_nonneg (le_of_lt ht1) (sub_nonneg.mpr hmx)
  have H2 : 0 ≤ (1 - t) * (y - m) := mul_nonneg (by linarith) (by linarith)
  have H3 : t * (x - m) + (1 - t) * (y - m) = 0 := by linarith
  have H4 : t * (x - m) = 0 := by linarith
  have H5 : x - m = 0 := by
    cases mul_eq_zero.mp H4 with
    | inl h_zero => exact False.elim (ne_of_lt ht1 h_zero.symm)
    | inr h_zero => exact h_zero
  left
  linarith
