import InfoGeometry.Spectrometry.WeightedQuadraticDescent

noncomputable section

namespace InfoGeometry.Spectrometry.WeiszfeldDescentLemma

open scoped BigOperators
open GeometricMedianCore

theorem weiszfeld_majorization {Space : Type*} [NormedAddCommGroup Space]
    (anchor candidate : Space) (regular : anchor ≠ 0) :
    ‖candidate‖ ≤ (‖candidate‖ ^ 2 + ‖anchor‖ ^ 2) / (2 * ‖anchor‖) := by
  apply (le_div_iff₀ (mul_pos two_pos (norm_pos_iff.mpr regular))).mpr
  nlinarith [sq_nonneg (‖candidate‖ - ‖anchor‖)]

variable {Line Space : Type*} [Fintype Line]
variable [NormedAddCommGroup Space] [InnerProductSpace ℝ Space]

def surrogate (observed : Line → Space) (anchor candidate : Space) : ℝ :=
  ∑ line, (‖candidate - observed line‖ ^ 2 + ‖anchor - observed line‖ ^ 2) /
    (2 * ‖anchor - observed line‖)

theorem surrogate_tangency (observed : Line → Space) (anchor : Space)
    (regular : RegularAt observed anchor) :
    surrogate observed anchor anchor = distanceObjective observed anchor := by
  apply Finset.sum_congr rfl
  intro line _
  have norm_ne : ‖anchor - observed line‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (sub_ne_zero.mpr (regular line))
  field_simp [norm_ne]
  <;> ring

theorem surrogate_majorization (observed : Line → Space) (anchor candidate : Space)
    (regular : RegularAt observed anchor) :
    distanceObjective observed candidate ≤ surrogate observed anchor candidate := by
  exact Finset.sum_le_sum (fun line _ =>
    weiszfeld_majorization _ _ (sub_ne_zero.mpr (regular line)))

theorem surrogate_eq_quadratic (observed : Line → Space) (anchor candidate : Space) :
    surrogate observed anchor candidate =
      weightedQuadratic (inverseDistance observed anchor) observed candidate / 2 +
        (∑ line, ‖anchor - observed line‖ ^ 2 / (2 * ‖anchor - observed line‖)) := by
  unfold surrogate weightedQuadratic inverseDistance
  rw [Finset.sum_div, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro line _
  ring

theorem step_minimizes_surrogate [Nonempty Line]
    (observed : Line → Space) (anchor candidate : Space)
    (regular : RegularAt observed anchor) :
    surrogate observed anchor (weiszfeldStep observed anchor) ≤
      surrogate observed anchor candidate := by
  have positive := inverse_distance_pos observed anchor regular
  have minimum := weightedCenter_minimizes_quadratic
    (inverseDistance observed anchor) observed candidate (fun line => (positive line).le)
    (ne_of_gt (mass_pos _ positive))
  rw [surrogate_eq_quadratic, surrogate_eq_quadratic]
  unfold weiszfeldStep
  linarith

theorem surrogate_gap [Nonempty Line]
    (observed : Line → Space) (anchor candidate : Space)
    (regular : RegularAt observed anchor) :
    surrogate observed anchor candidate =
      surrogate observed anchor (weiszfeldStep observed anchor) +
        (∑ line, inverseDistance observed anchor line) / 2 *
          ‖candidate - weiszfeldStep observed anchor‖ ^ 2 := by
  have positive := inverse_distance_pos observed anchor regular
  rw [surrogate_eq_quadratic, surrogate_eq_quadratic,
    weightedQuadratic_completed_square _ _ candidate (ne_of_gt (mass_pos _ positive))]
  unfold weiszfeldStep
  ring

theorem surrogate_minimum_unique [Nonempty Line]
    (observed : Line → Space) (anchor candidate : Space)
    (regular : RegularAt observed anchor) :
    surrogate observed anchor candidate =
        surrogate observed anchor (weiszfeldStep observed anchor) ↔
      candidate = weiszfeldStep observed anchor := by
  rw [surrogate_gap observed anchor candidate regular, add_eq_left]
  have positive := div_pos (mass_pos _ (inverse_distance_pos observed anchor regular)) two_pos
  rw [mul_eq_zero, or_iff_right positive.ne', sq_eq_zero_iff, norm_eq_zero, sub_eq_zero]

theorem weiszfeld_quantitative_descent [Nonempty Line]
    (observed : Line → Space) (anchor : Space) (regular : RegularAt observed anchor) :
    distanceObjective observed (weiszfeldStep observed anchor) +
        (∑ line, inverseDistance observed anchor line) / 2 *
          ‖anchor - weiszfeldStep observed anchor‖ ^ 2 ≤ distanceObjective observed anchor := by
  have major := surrogate_majorization observed anchor (weiszfeldStep observed anchor) regular
  have gap := surrogate_gap observed anchor anchor regular
  rw [surrogate_tangency observed anchor regular] at gap
  linarith

theorem weiszfeld_monotone_descent [Nonempty Line]
    (observed : Line → Space) (anchor : Space) (regular : RegularAt observed anchor) :
    distanceObjective observed (weiszfeldStep observed anchor) ≤ distanceObjective observed anchor := by
  calc
    _ ≤ surrogate observed anchor (weiszfeldStep observed anchor) :=
      surrogate_majorization observed anchor _ regular
    _ ≤ surrogate observed anchor anchor := step_minimizes_surrogate observed anchor anchor regular
    _ = _ := surrogate_tangency observed anchor regular

theorem weiszfeld_strict_descent [Nonempty Line]
    (observed : Line → Space) (anchor : Space) (regular : RegularAt observed anchor)
    (not_fixed : weiszfeldStep observed anchor ≠ anchor) :
    distanceObjective observed (weiszfeldStep observed anchor) < distanceObjective observed anchor := by
  have decrement := mul_pos
    (div_pos (mass_pos _ (inverse_distance_pos observed anchor regular)) two_pos)
    (sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr not_fixed.symm)))
  have descent := weiszfeld_quantitative_descent observed anchor regular
  linarith

theorem weiszfeld_energy_eq_iff_fixed [Nonempty Line]
    (observed : Line → Space) (anchor : Space) (regular : RegularAt observed anchor) :
    distanceObjective observed (weiszfeldStep observed anchor) = distanceObjective observed anchor ↔
      weiszfeldStep observed anchor = anchor := by
  constructor
  · intro equal
    by_contra not_fixed
    exact (ne_of_lt (weiszfeld_strict_descent observed anchor regular not_fixed)) equal
  · intro fixed
    rw [fixed]

end InfoGeometry.Spectrometry.WeiszfeldDescentLemma
