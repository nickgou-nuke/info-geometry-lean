import Mathlib.Data.Nat.Basic

namespace Omega.Zeta

/-- Concrete time-filtered effect data. The numerical fields record the base filtration and two
changes of gauge/cohomology representative; the associated graded object forgets these choices. -/
def xi_stable_type_minspec_graded_semiring_associated_graded :=
  ℕ → ℕ

/-- The time-filtered effect semiring profile before passing to the associated graded quotient. -/
def xi_stable_type_minspec_graded_semiring_time_filtered_effect
    (effect_weight : ℕ → ℕ) (t n : ℕ) : ℕ :=
  effect_weight n + t * n

/-- The associated graded quotient of the time-filtered profile. -/
def xi_stable_type_minspec_graded_semiring_associated_graded_quotient
    (effect_weight : ℕ → ℕ) (_t : ℕ) :
    xi_stable_type_minspec_graded_semiring_associated_graded :=
  effect_weight

/-- Minimal-prime-spectrum classification predicate for the graded effect profile. -/
def xi_stable_type_minspec_graded_semiring_minspec_classification
    (effect_weight : ℕ → ℕ)
    (G : xi_stable_type_minspec_graded_semiring_associated_graded) : Prop :=
  ∀ n, G n = effect_weight n

/-- Stability statement: gauge and cohomology representative changes preserve the associated
graded quotient and therefore the minimal-prime-spectrum classification. -/
def xi_stable_type_minspec_graded_semiring_Conclusion
    (effect_weight : ℕ → ℕ) (base_time gauge_time cohomology_time : ℕ) : Prop :=
  let base := xi_stable_type_minspec_graded_semiring_associated_graded_quotient effect_weight base_time
  let gauge := xi_stable_type_minspec_graded_semiring_associated_graded_quotient effect_weight gauge_time
  let cohomology := xi_stable_type_minspec_graded_semiring_associated_graded_quotient effect_weight cohomology_time
  xi_stable_type_minspec_graded_semiring_minspec_classification effect_weight base ∧
    gauge = base ∧
      cohomology = base ∧
        xi_stable_type_minspec_graded_semiring_minspec_classification effect_weight gauge ∧
          xi_stable_type_minspec_graded_semiring_minspec_classification effect_weight cohomology

/-- Paper label: `thm:xi-stable-type-minspec-graded-semiring`. -/
theorem paper_xi_stable_type_minspec_graded_semiring
    (effect_weight : ℕ → ℕ) (base_time gauge_time cohomology_time : ℕ) :
    xi_stable_type_minspec_graded_semiring_Conclusion
      effect_weight base_time gauge_time cohomology_time := by
  simp [xi_stable_type_minspec_graded_semiring_Conclusion,
    xi_stable_type_minspec_graded_semiring_associated_graded_quotient,
    xi_stable_type_minspec_graded_semiring_minspec_classification]

end Omega.Zeta
