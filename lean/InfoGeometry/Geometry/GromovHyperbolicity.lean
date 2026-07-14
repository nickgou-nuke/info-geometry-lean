import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace GromovHyperbolicity

variable {X : Type*} [PseudoMetricSpace X]

/-- The Gromov product `(x,y)_e = (d(e,x)+d(e,y)-d(x,y))/2`. -/
noncomputable def gromovProductAt (e x y : X) : ℝ :=
  (dist e x + dist e y - dist x y) / 2

/-- AFP `Gromov_hyperbolic_subset`: the four-point definition of `δ`-hyperbolicity. -/
def GromovHyperbolicSubset (δ : ℝ) (A : Set X) : Prop :=
  ∀ x ∈ A, ∀ y ∈ A, ∀ z ∈ A, ∀ t ∈ A,
    dist x y + dist z t ≤
      max (dist x z + dist y t) (dist x t + dist y z) + 2 * δ

lemma GromovHyperbolicSubset.intro {δ : ℝ} {A : Set X}
    (h : ∀ x y z t, x ∈ A → y ∈ A → z ∈ A → t ∈ A →
      dist x y + dist z t ≤
        max (dist x z + dist y t) (dist x t + dist y z) + 2 * δ) :
    GromovHyperbolicSubset δ A := by
  intro x hx y hy z hz t ht
  exact h x y z t hx hy hz ht

@[simp]
lemma gromovProductAt_comm (e x y : X) :
    gromovProductAt e x y = gromovProductAt e y x := by
  unfold gromovProductAt
  rw [dist_comm x y]
  ring

lemma gromovProductAt_nonneg (e x y : X) :
    0 ≤ gromovProductAt e x y := by
  unfold gromovProductAt
  have h : dist x y ≤ dist e x + dist e y := by
    simpa [dist_comm x e] using dist_triangle x e y
  linarith

lemma gromovProductAt_le_left (e x y : X) :
    gromovProductAt e x y ≤ dist e x := by
  unfold gromovProductAt
  have h : dist e y ≤ dist e x + dist x y := dist_triangle e x y
  linarith

lemma gromovProductAt_le_right (e x y : X) :
    gromovProductAt e x y ≤ dist e y := by
  rw [gromovProductAt_comm e x y]
  exact gromovProductAt_le_left e y x

@[simp]
lemma gromovProductAt_self (e x : X) :
    gromovProductAt e x x = dist e x := by
  simp [gromovProductAt]

lemma gromovProductAt_add_swap_base (e x y : X) :
    gromovProductAt e x y + gromovProductAt x e y = dist e x := by
  unfold gromovProductAt
  rw [dist_comm x e]
  ring

/-- A `δ`-hyperbolic subset satisfies the four-point inequality for each quadruple in it. -/
lemma GromovHyperbolicSubset.quad_ineq {δ : ℝ} {A : Set X}
    (hA : GromovHyperbolicSubset δ A) {x y z t : X}
    (hx : x ∈ A) (hy : y ∈ A) (hz : z ∈ A) (ht : t ∈ A) :
    dist x y + dist z t ≤
      max (dist x z + dist y t) (dist x t + dist y z) + 2 * δ :=
  hA x hx y hy z hz t ht

/--
AFP `Gromov_hyperbolic_subsetI2`: the Gromov-product inequality implies
the four-point definition of `δ`-hyperbolicity.
-/
lemma GromovHyperbolicSubset.of_gromovProduct {δ : ℝ} {A : Set X}
    (h : ∀ e ∈ A, ∀ x ∈ A, ∀ y ∈ A, ∀ z ∈ A,
      gromovProductAt e x z ≥
        min (gromovProductAt e x y) (gromovProductAt e y z) - δ) :
    GromovHyperbolicSubset δ A := by
  intro x hx y hy z hz t ht
  have hp := h x hx z hz y hy t ht
  unfold gromovProductAt at hp
  by_cases hmin : (dist x z + dist x y - dist z y) / 2 ≤
      (dist x y + dist x t - dist y t) / 2
  · have hmin_eq : min ((dist x z + dist x y - dist z y) / 2)
        ((dist x y + dist x t - dist y t) / 2) =
        (dist x z + dist x y - dist z y) / 2 := min_eq_left hmin
    rw [hmin_eq] at hp
    rw [dist_comm z y] at hp
    have hmax :
        dist x t + dist y z ≤ max (dist x z + dist y t) (dist x t + dist y z) :=
      le_max_right _ _
    linarith
  · have hle : (dist x y + dist x t - dist y t) / 2 ≤
      (dist x z + dist x y - dist z y) / 2 := le_of_not_ge hmin
    have hmin_eq : min ((dist x z + dist x y - dist z y) / 2)
        ((dist x y + dist x t - dist y t) / 2) =
        (dist x y + dist x t - dist y t) / 2 := min_eq_right hle
    rw [hmin_eq] at hp
    have hmax :
        dist x z + dist y t ≤ max (dist x z + dist y t) (dist x t + dist y z) :=
      le_max_left _ _
    linarith

end GromovHyperbolicity
